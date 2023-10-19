from z3 import *
from collections import defaultdict

from unified_planning.shortcuts import *
from unified_planning.engines import CompilationKind
from unified_planning.model.operators import *
from unified_planning.model.walkers import *

from ._encodingsUtils import *

class LinearEncoding:
    def __init__(self, task, cfg):
        self.task     = task

        self.modifer_encoder = {
            'linear': self._encodeLinearModifier,
            'parallel': self._encodeParallelModifier
        }

        self.mutexes_generator = {
            'linear': self._computeSerialMutexes,
            'parallel': self._computeParallelMutexes
        }

        self.modifier = self.modifer_encoder[cfg.gets('modifier', 'linear')]
        self.mutexes_generator = self.mutexes_generator[cfg.gets('modifier', 'linear')]

        self.z3_action_variables          = defaultdict(dict)
        self.z3_problem_variables         = defaultdict(dict)
        self.z3_problem_constant_numerics = defaultdict(dict)

        self.z3_variables = defaultdict(dict)
        self.z3_constants = defaultdict(dict)
        self.formula      = defaultdict(dict)

        self.all_problem_fluents = []

        self.grounding_results = self._ground()
        self.ground_problem = self.grounding_results.problem

        self.mutexes        = self.mutexes_generator()
                
    def _ground(self):
        with Compiler(problem_kind=self.task.kind, compilation_kind=CompilationKind.GROUNDING) as grounder:
            return grounder.compile(self.task, compilation_kind=CompilationKind.GROUNDING)
    
    def _computeSerialMutexes(self):
        # Stores mutexes
        mutexes = []
        for a1 in self.ground_problem.actions:
            for a2 in self.ground_problem.actions:
                # Skip same action
                if not a1.name == a2.name:
                    mutexes.append((a1,a2))
        return mutexes

    def _computeParallelMutexes(self):
        """!
        Computes mutually exclusive actions:
        Two actions (a1, a2) are mutex if:
            - intersection pre_a1 and eff_a2 (or viceversa) is non-empty
            - intersection between eff_a1+ and eff_a2- (or viceversa) is non-empty
            - intersection between numeric effects is non-empty

        See, e.g., 'A Compilation of the Full PDDL+ Language into SMT'', Cashmore et al.

        @return mutex: list of tuples defining action mutexes
        """

        def get_add_del_effects(action):
            """!
            Returns a tuple (add, del) of lists of effects of the action
            """
            
            del_effects = []
            effects_fluents = [effect for effect in action.effects if effect.value.type.is_bool_type()]

            add_effects = set([str(eff.fluent) for eff in effects_fluents if eff.value.is_true()])
            del_effects = set([str(eff.fluent) for eff in effects_fluents if not eff.value.is_true()])

            return (add_effects, del_effects)
        
        def get_numeric_effects(action):
            """!
            Returns a set of numeric effects of the action
            """            
            return set([str(effect.fluent) for effect in action.effects if effect.value.type.is_int_type() or effect.value.type.is_real_type()])

        def get_preconditions(action):
            """!
            Returns a set of preconditions of the action
            """            
            preconditions = set()
            for pre in action.preconditions:
                for arg in pre.args:
                    if arg.node_type == OperatorKind.FLUENT_EXP:
                        preconditions.add(str(arg))
            return preconditions

        mutexes = set()
        
        for action_1 in self.ground_problem.actions:
            add_a1, del_a1 = get_add_del_effects(action_1)
            num_1 = get_numeric_effects(action_1)
            pre_1 = get_preconditions(action_1)

            for action_2 in self.ground_problem.actions:
                if not action_1.name == action_2.name:
                  
                    add_a2, del_a2 = get_add_del_effects(action_2)
                    num_2 = get_numeric_effects(action_2)
                    pre_2 = get_preconditions(action_2)

                    ## Condition 1
                    if len(pre_1.intersection(add_a2)) > 0 or len(pre_1.intersection(del_a2)) > 0:
                        mutexes.add((action_1, action_2))

                    if len(pre_2.intersection(add_a1)) > 0 or len(pre_2.intersection(del_a1)) > 0:
                        mutexes.add((action_1, action_2))

                    ## Condition 2
                    if len(add_a1.intersection(del_a2)) > 0:
                        mutexes.add((action_1, action_2))
                    
                    if len(add_a2.intersection(del_a1)) > 0:
                        mutexes.add((action_1, action_2))

                    ## Condition 3
                    if num_1 & num_2:
                        mutexes.add((action_1, action_2))

                    pass

        return mutexes

    def _encodeParallelModifier(self, variables, mutexes, bound):
        c = []
        for step in range(bound):
            for pair in mutexes:
                c.append(z3.Or(z3.Not(variables[step][pair[0].name]), z3.Not(variables[step][pair[1].name])))
        return c

    def _encodeLinearModifier(self, variables, bound):
        c = []
        for step in range(bound):
            pbc = [(var,1) for var in variables[step].values()]
            c.append(z3.PbLe(pbc,1))
        return c

    def getAction(self, step, name):
        return self.z3_action_variables[step][name]

    def getActionsList(self):
        return self.ground_problem.actions

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

        for step in range(start_step, end_step):
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
        
        self.all_problem_fluents.extend(variable_numeric_fluents)
        self.all_problem_fluents.extend(variable_boolean_fluents)
        # Now remove constant fluents from all_problem_fluents.
        for fluent in constant_fluents:
            if fluent in self.all_problem_fluents:
                self.all_problem_fluents.remove(fluent)
      
    def encodeInitialState(self):
        """!
        Encodes formula defining initial state

        @return initial: Z3 formula asserting initial state
        """
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
        return inorderTraverse(self.ground_problem.goals, self.z3_problem_variables, horizon, self.z3_problem_constant_numerics)

    def encodeActions(self, start_step, end_step):

        actions = []
        for step in range(start_step, end_step):
            for action in self.ground_problem.actions:
                # Append preconditions
                for pre in action.preconditions:
                    precondition = inorderTraverse(pre, self.z3_problem_variables, step, self.z3_problem_constant_numerics)
                    actions.append(z3.Implies(self.z3_action_variables[step][action.name], precondition))

                # Append effects.
                for effect in action.effects:
                    _eff = inorderTraverse(effect, self.z3_problem_variables, step, self.z3_problem_constant_numerics)
                    actions.append(z3.Implies(self.z3_action_variables[step][action.name], _eff))
                    
                if len(action.conditional_effects) > 0:
                    raise Exception("Conditional effects are not supported yet")

        return actions

    def encodeFrame(self, start_step, end_step):
        """!
        Encode explanatory frame axioms: a predicate retains its value unless
        it is modified by the effects of an action.

        @return frame: list of frame axioms
        """

        frame = []

        # Create new object and use it as
        # inadmissible value to check if
        # variable exists in dictionary

        sentinel = object()

        for step in range(start_step, end_step):
            # Encode frame axioms for boolean fluents
            for fluent in self.all_problem_fluents:
                if fluent.type.is_bool_type():
                    fluent_pre  = self.z3_problem_variables[step].get(str(fluent), sentinel)
                    fluent_post = self.z3_problem_variables[step+1].get(str(fluent), sentinel)
                    # Encode frame axioms only if atoms have SMT variables associated
                    if fluent_pre is not sentinel and fluent_post is not sentinel:
                        action_add = []
                        action_del = []

                        for action in self.ground_problem.actions:
                            effects_fluents = [effect for effect in action.effects if effect.value.type.is_bool_type()]
                            
                            for ele in effects_fluents:
                                if str(ele.fluent) == str(fluent):
                                    if ele.value.is_true():
                                        action_add.append(self.z3_action_variables[step][action.name])
                                    else:
                                        action_del.append(self.z3_action_variables[step][action.name])

                        frame.append(z3.Implies(z3.And(z3.Not(fluent_pre),fluent_post),z3.Or(action_add)))
                        frame.append(z3.Implies(z3.And(fluent_pre,z3.Not(fluent_post)),z3.Or(action_del)))

                elif fluent.type.is_int_type() or fluent.type.is_real_type():
                    fluent_pre  = self.z3_problem_variables[step].get(str(fluent), sentinel)
                    fluent_post = self.z3_problem_variables[step+1].get(str(fluent), sentinel)
                    if fluent_pre is not sentinel and fluent_post is not sentinel:
                        action_num = []
                        for action in self.ground_problem.actions:
                            effects_fluents = [effect for effect in action.effects if effect.value.type.is_int_type() or effect.value.type.is_real_type()]
                            for ele in effects_fluents:
                                if str(ele.fluent) == str(fluent):
                                    action_num.append(self.z3_action_variables[step][action.name])
                            
                        #TODO
                        # Can we write frame axioms for num effects in a more
                        # efficient way?
                        frame.append(z3.Or(fluent_post == fluent_pre, z3.Or(action_num)))
                else:
                    raise Exception("Unknown fluent type {}".format(fluent.type))

        return frame

    def encodeExecutionSemantics(self, horizon):       
        try:
            return self.modifier(self.z3_action_variables, horizon)
        except:
            return self.modifier(self.z3_action_variables, self.mutexes, horizon)

    def encodePlanLength(self, plan_length):
        return []
        
    def encodeMinimsation(self):
        return []

    def encode(self,horizon):

        start_index = 0 if len(self.z3_problem_variables) == 0 else len(self.z3_problem_variables)-1      

        # Create variables
        self.createVariables(start_index, horizon)

        # Start encoding formula
        formula = defaultdict(list)

        # Encode initial state axioms
        formula['initial'] = self.encodeInitialState()

        # Encode goal state axioms
        formula['goal'] = self.encodeGoalState(horizon)

        # Encode universal axioms
        formula['actions'] = self.encodeActions(start_index, horizon)

        # Encode explanatory frame axioms
        formula['frame'] = self.encodeFrame(start_index, horizon)

        # Encode execution semantics (linear)
        formula['sem'] = self.encodeExecutionSemantics(horizon)

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
                else:
                    self.formula[key].extend(formula[key])
        # We want to return the extedned version of the formula.
        return formula, self.formula
