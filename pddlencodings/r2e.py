from z3 import *
from collections import defaultdict
from collections import deque

from unified_planning.shortcuts import *
from unified_planning.engines import CompilationKind
from unified_planning.model.operators import *
from unified_planning.model.walkers import *

from ._encodingsUtils import *

class R2EEncoding:
    def __init__(self, task, cfg=defaultdict(dict)): 
        self.task = task
        self.grounding_results = self._ground()
        self.ground_problem = self.grounding_results.problem

        self.grounded_goals = self.getSoretedGroundedGoals()

        self.z3_action_variables          = defaultdict(dict)
        self.z3_problem_variables         = defaultdict(dict)
        self.z3_problem_constant_numerics = defaultdict(dict)

        self.z3_chain_variables_actions   = defaultdict(dict)

        self.z3_variables = defaultdict(dict)
        self.z3_constants = defaultdict(dict)
        self.formula      = defaultdict(dict)
        
    def _ground(self):
        # Ground the task.
        with Compiler(problem_kind=self.task.kind, compilation_kind=CompilationKind.GROUNDING) as grounder:
            self.groundername = grounder.name    
            return grounder.compile(self.task, compilation_kind=CompilationKind.GROUNDING)

    def getAction(self, step, name):
        return self.z3_action_variables[step][name]
    
    def getFormula(self):
        return self.formula
    
    def createVariables(self, start_step, end_step):

        # MF: I hate this but the only way to get grounded functions parsing the initial values
        boolean_fluents = [f for f in self.ground_problem.initial_values if f.type.is_bool_type()]
        for step in range(start_step, end_step+1):
            for fluent in boolean_fluents:
                fluentname = str(fluent)
                self.z3_problem_variables[step][fluentname] = z3.Bool('{}_${}'.format(fluentname,step))
        
        numeric_fluents = [f for f in self.ground_problem.initial_values if f.type.is_int_type() or f.type.is_real_type()]

        # The grounder does not replace the constants in the problem, therefore we can do that by listing the 
        # predicates that are not modified by any action.
        # We need to check the effects for each action and see if the predicate is modified.
        constant_fluents = [f for f in numeric_fluents]
        for action in self.ground_problem.actions:
            for effect in action.effects:
                if effect.kind in [EffectKind.INCREASE, EffectKind.DECREASE, EffectKind.ASSIGN]:
                    if effect.fluent in constant_fluents:
                        constant_fluents.remove(effect.fluent)
        
        # Get the values for those constants to replace them in the problem.
        for fluent in constant_fluents:
            # A hacky way to ge the value of the constant.
            self.z3_problem_constant_numerics[str(fluent)] = float(str(self.ground_problem.initial_values[fluent]))

        # Now create z3 variables for the numeric fluents.
        for step in range(start_step, end_step+1):
            for fluent in numeric_fluents:
                if not fluent in constant_fluents:
                    self.z3_problem_variables[step][str(fluent)] = z3.Real('{}_${}'.format(str(fluent),step))

        # self.z3_variables
        variable_numeric_fluents = [f for f in self.ground_problem.initial_values if f.type.is_int_type() or f.type.is_real_type()]
        variable_numeric_fluents = [ele for ele in variable_numeric_fluents if ele not in constant_fluents]
        variable_boolean_fluents = [f for f in self.ground_problem.initial_values if f.type.is_bool_type()]

        fluents_used_in_actions = set()

        for step in range(start_step, end_step+1):
            for action in self.ground_problem.actions:
                self.z3_action_variables[step][action.name] = z3.Bool('{}_${}'.format(action.name,step))
                if step == 1:
                    for pre in action.preconditions:
                        precondition = inorderTraverse(pre, self.z3_problem_variables, 0, self.z3_problem_constant_numerics)
                        collectOperandsInExpression(precondition, fluents_used_in_actions)
                    for eff in action.effects:
                        effect = inorderTraverse(eff, self.z3_problem_variables, 0, self.z3_problem_constant_numerics)
                        collectOperandsInExpression(effect, fluents_used_in_actions)

        for var in variable_numeric_fluents:
            if str(var) in fluents_used_in_actions:
                self.z3_variables[str(var)] = z3.Real(str(var))
        for var in variable_boolean_fluents:
            if str(var) in fluents_used_in_actions:
                self.z3_variables[str(var)] = z3.Bool(str(var))

        for const in constant_fluents:
            self.z3_constants[str(const)] = z3.RealVal(float(str(self.ground_problem.initial_values[const])))
      
    def encodeInitialState(self):

        initial = []

        for fluent in self.ground_problem.initial_values:
            if str(fluent) in list(self.z3_problem_constant_numerics.keys()):
                continue
            if fluent.type.is_bool_type():
                if self.ground_problem.initial_values[fluent].is_true():
                    initial.append(self.z3_problem_variables[0][str(fluent)])
                else:
                    initial.append(z3.Not(self.z3_problem_variables[0][str(fluent)]))
            elif fluent.type.is_int_type() or fluent.type.is_real_type():
                fluent_name = str(fluent)
                if fluent.node_type == OperatorKind.FLUENT_EXP:
                   initial.append(self.z3_problem_variables[0][fluent_name] == self.ground_problem.initial_values[fluent])
                else:
                    #throw an error
                    raise Exception("Fluent {} is not a fluent expression".format(fluent_name))
            else:
                # we skip initial facts that do not involve numeric fluents
                raise Exception("Fluent {} is not a boolean or numeric fluent".format(fluent_name))
           
        return initial
    
    def encodeGoalState(self, horizon):

        # Collect the chain variables.
        gchainvars = []
        for varname, var in self.z3_problem_variables[horizon].items():
            if varname in self.z3_chain_variables_actions[horizon-1]:
                gchainvars.append((var, self.z3_chain_variables_actions[horizon-1][varname][-1]))

        chained_goal_predicates = []
        goalstate = inorderTraverse(self.ground_problem.goals, self.z3_problem_variables, horizon, self.z3_problem_constant_numerics)
        goal_predicates = [goalstate] #if len(self.ground_problem.goals) == 1 else goalstate
        for g in goal_predicates:
            for chainvar in gchainvars:
                g = z3.substitute(g, chainvar)
            chained_goal_predicates.append(g)

        # Now we need to link those predicates to the t+1 variables in the chain encoding.
        return chained_goal_predicates

    def getActionsList(self):
        # Later, we can implement a function that returns the ordering of the actions which could be 
        # informative. But for now, we will return a sorted action names.
        return sorted([action for action in self.ground_problem.actions], key=lambda x: x.name)

    def getActionIndex(self, action):
        actionlist = [a.name for a in self.getActionsList()]
        return actionlist.index(action)
    
    def getSoretedGroundedGoals(self):
        sorted_goals = []
        # We need to sort the goals based on the same ordering we have in the actionlist.
        subgoals = []
        for goal in self.ground_problem.goals:
            subgoals.extend(list(goal.args))

        sorted_actions = self.getActionsList()
        for action in sorted_actions:
            for eff in action.effects:
                if eff.fluent in subgoals and not eff.fluent in sorted_goals:
                    sorted_goals.append(eff.fluent)
        sorted_goals.reverse()
        return sorted_goals
    
    def encodeActionsChain(self, start_step, end_step):
        
        actions_chain_encoding = []
        actions_ordering = self.getActionsList()

        # Create the variables for the first step
        if start_step == 0:
            for varname, var in self.z3_variables.items():
                if not isinstance(var.sort(), z3.z3.BoolSortRef) and not isinstance(var.sort(), z3.z3.ArithSortRef):
                    raise Exception("Variable {} is not a boolean or numeric variable".format(varname))
                if not varname in self.z3_chain_variables_actions[-1]:
                    self.z3_chain_variables_actions[-1][varname] = deque()
                    self.z3_chain_variables_actions[-1][varname].append(self.z3_problem_variables[0][varname])

        for step in range(start_step, end_step):
            for idx, action in enumerate(actions_ordering):

                for pre in action.preconditions:
                    precondition = inorderTraverse(pre, self.z3_problem_variables, step, self.z3_problem_constant_numerics)
                    # Update the precondition with the new variables.
                    vars_to_update = parseZ3FormulaAndReturnReplacementVariables(precondition, self.z3_chain_variables_actions)
                    for _varname, exprvar, newvar in vars_to_update:
                        precondition = z3.substitute(precondition, (exprvar, newvar[-1]))

                    actions_chain_encoding.append(z3.Implies(self.z3_action_variables[step][action.name], precondition))

                replacement_vars    = []
                for effect in action.effects:
                    newVariableName = getZ3VariableName(effect.fluent)
                    
                    # 1. Create a new variable with this action name in this step.
                    if not newVariableName in self.z3_chain_variables_actions[step]:
                        self.z3_chain_variables_actions[step][newVariableName] = deque()
                        
                    if isinstance(self.z3_chain_variables_actions[step-1][newVariableName][-1].sort(), z3.z3.ArithSortRef):
                        _effz3var = z3.Real('{}_${}_${}'.format(newVariableName,action.name,step))  
                    else:
                        _effz3var = z3.Bool('{}_${}_${}'.format(newVariableName,action.name,step))
                    
                    # append if the created variable is not the same as the previous one.
                    if len(self.z3_chain_variables_actions[step][newVariableName]) == 0 or not self.z3_chain_variables_actions[step][newVariableName][-1] == _effz3var:
                        self.z3_chain_variables_actions[step][newVariableName].append(_effz3var)

                    # 2. Then for the R.H.S of the effect expression, we need to update the variables with
                    # the chained ones if available in this step of the pervious one.
                    # We can create a tuple with the old variable with the new one.

                    _tmp, z3EffectValue  = getZ3Effect(effect, self.z3_problem_variables, step, self.z3_problem_constant_numerics)
                    operands = [z3EffectValue] if len(z3EffectValue.children()) == 0 else z3EffectValue.children()

                    # There could be the case where one of the operands is an arithmetic operation.
                    # We need to check that and add it to the operands list.
                    _expanded_list = []
                    flattenEffect(z3EffectValue, _expanded_list)
                    for operand in _expanded_list:
                        # This operand could have been created in this step of the pervious one.
                        # We need to check that.
                        operandname = getZ3VariableName(operand)
                        if operandname in self.z3_chain_variables_actions[step]:
                            if operandname == newVariableName and len(self.z3_chain_variables_actions[step][operandname]) > 1:
                                # This is the variable we just created.
                                # We need to update the expression with the new variable.
                                replacement_vars.append((newVariableName, operand, self.z3_chain_variables_actions[step][operandname][-2]))
                            elif operandname == newVariableName and len(self.z3_chain_variables_actions[step][operandname]) == 1:
                                # This is the variable we just created.
                                # We need to update the expression with the new variable.
                                replacement_vars.append((newVariableName, operand, self.z3_chain_variables_actions[step-1][operandname][-1]))
                            else:
                                # This is a variable that was created in a previous step.
                                # We need to update the expression with the new variable.
                                replacement_vars.append((newVariableName, operand, self.z3_chain_variables_actions[step][operandname][-1]))
                        elif operandname in self.z3_chain_variables_actions[step-1]:
                            # This is a variable that was created in a previous step.
                            # We need to update the expression with the new variable.
                            replacement_vars.append((newVariableName, operand, self.z3_chain_variables_actions[step-1][operandname][-1]))

                arithemtic_exprs, boolean_expr = getArithBoolExprs(action.effects, self.z3_problem_variables, step, self.z3_problem_constant_numerics)

                # Now it is much easier to replace the variables.

                for arithmetic_expr in arithemtic_exprs:
                    # collect all replace vars for this expression.
                    varname = arithmetic_expr[0]
                    expr = arithmetic_expr[1]
                    replace_expr_list = [var for var in replacement_vars if var[0] == arithmetic_expr[0]]
                    for _varname, oldvar, newvar in replace_expr_list:
                        expr = z3.substitute(expr, (oldvar, newvar))
                    # Now we need to add the expression to the chain encoding.
                    actions_chain_encoding.append(z3.Implies(self.z3_action_variables[step][action.name], self.z3_chain_variables_actions[step][varname][-1] == expr))

                    if len(self.z3_chain_variables_actions[step][varname]) > 1:
                        actions_chain_encoding.append(z3.Implies(z3.Not(self.z3_action_variables[step][action.name]), self.z3_chain_variables_actions[step][varname][-1] == self.z3_chain_variables_actions[step][varname][-2]))
                    else:
                        actions_chain_encoding.append(z3.Implies(z3.Not(self.z3_action_variables[step][action.name]), self.z3_chain_variables_actions[step][varname][-1] == self.z3_chain_variables_actions[step-1][varname][-1]))

                for boolean_expr in boolean_expr:
                    # collect all replace vars for this expression.
                    varname = boolean_expr[0]
                    expr = boolean_expr[1]
                    replace_expr_list = [var for var in replacement_vars if var[0] == boolean_expr[0]]
                    for _varname, oldvar, newvar in replace_expr_list:
                        expr = z3.substitute(expr, (oldvar, newvar))
                    # Now we need to add the expression to the chain encoding.
                    # For booleans the variable should be the same as the expression.
                    
                    if expr.decl().kind() == z3.Z3_OP_NOT:
                        actions_chain_encoding.append(z3.Implies(self.z3_action_variables[step][action.name], self.z3_chain_variables_actions[step][varname][-1] == z3.BoolVal(False)))
                    else:
                        actions_chain_encoding.append(z3.Implies(self.z3_action_variables[step][action.name], self.z3_chain_variables_actions[step][varname][-1] == z3.BoolVal(True)))
                    
                    # Chaining the varibale if the action is not enabled.
                    if len(self.z3_chain_variables_actions[step][varname]) > 1:
                        actions_chain_encoding.append(z3.Implies(z3.Not(self.z3_action_variables[step][action.name]), self.z3_chain_variables_actions[step][varname][-1] == self.z3_chain_variables_actions[step][varname][-2]))
                    else:
                        actions_chain_encoding.append(z3.Implies(z3.Not(self.z3_action_variables[step][action.name]), self.z3_chain_variables_actions[step][varname][-1] == self.z3_chain_variables_actions[step-1][varname][-1]))
        
        return actions_chain_encoding
    
    def encodeMinimsation(self):
        _actions_to_int = []
        for _step, _actions in self.z3_action_variables.items():
            _actions_to_int.extend([z3.If(var, z3.RealVal(1.0), z3.RealVal(0.0)) for var in _actions.values()])
        return z3.Sum(_actions_to_int)

    def encode(self, horizon):

        start_index = 0 if len(self.z3_problem_variables) == 0 else len(self.z3_problem_variables)-1      

        formula = defaultdict(list)
        # Note that we add a +1 to the horizon since the first iteration creates the chain variables list.
        self.createVariables(start_index, horizon)

        # Encode actions chain axioms
        formula['actions'] = self.encodeActionsChain(start_index, horizon)

        # Encode initial state axioms at the first instance.
        formula['initial'] = self.encodeInitialState()

        # Encode goal state axioms
        formula['goal'] = self.encodeGoalState(horizon)

        # Encode plan length
        # This should be done after finding a solution.
        formula['objective'] = self.encodeMinimsation()

        if start_index == 0:
            self.formula = formula
        else:
            for key in self.formula:
                # Skip the initial case
                if key == 'initial':
                    continue
                # if goal state then update it with the new goal state
                elif key == 'goal':
                    self.formula[key] = formula[key]
                elif key == 'objective':
                    self.formula[key] = formula[key]
                else:
                    self.formula[key].extend(formula[key])
        # We want to return the extedned version of the formula.
        return formula, self.formula