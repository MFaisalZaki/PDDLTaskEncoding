##
# @file

############################################################################
##    This file is part of OMTPlan.
##
##    OMTPlan is free software: you can redistribute it and/or modify
##    it under the terms of the GNU General Public License as published by
##    the Free Software Foundation, either version 3 of the License, or
##    (at your option) any later version.
##
##    OMTPlan is distributed in the hope that it will be useful,
##    but WITHOUT ANY WARRANTY; without even the implied warranty of
##    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##    GNU General Public License for more details.
##
##    You should have received a copy of the GNU General Public License
##    along with OMTPlan.  If not, see <https://www.gnu.org/licenses/>.
############################################################################
import os
import json
import re

from z3 import *
from unified_planning.model.operators import *
from unified_planning.model.walkers import *
from unified_planning.shortcuts import *

import unified_planning

def flattenEffect(eff, ret_list):
    if len(eff.children()) == 0:
        ret_list.append(eff)
    else:
        for child in eff.children():
            flattenEffect(child, ret_list)
    return

def getAllOperandsInExpression(expr):
    operandsnames = set()
    collectOperandsInExpression(expr, operandsnames)
    return operandsnames

def parseZ3FormulaAndReturnReplacementVariables(formula, chain_variable_list):
    operandsnames = getAllOperandsInExpression(formula)
    return_list = []
    for operand in operandsnames:
        operand_last_creation = []
        for step, vars_queue in chain_variable_list.items():
            if operand in vars_queue:
                operand_last_creation.append(vars_queue[operand][-1])
        if len(operand_last_creation) > 0:
            return_list.append((operand, getZ3VariableFromExpressionWithName(formula, operand), operand_last_creation))
    return return_list

def getZ3VariableFromExpressionWithName(expr, varname):
    
    expr_children = [expr] if len(expr.children()) == 0 else expr.children()
    for idx, child in enumerate(expr_children):
        # First lets loop on the children
        if is_const(child) and getZ3VariableName(child) == varname:
            return child
        elif is_const(child) and not getZ3VariableName(child) == varname:
            continue
        else:
            ret = getZ3VariableFromExpressionWithName(child, varname)
            if ret is not None:
                return ret

def collectOperandsInExpression(expr, variables):
    if is_const(expr) and expr.decl().kind() == Z3_OP_UNINTERPRETED:
        variables.add(getZ3VariableName(expr))
    elif is_app(expr):
        for arg in expr.children():
            collectOperandsInExpression(arg, variables)

def getZ3VariableName(fluent):
    """!
    Returns Z3 variable name for a given fluent.

    @param fluent: PDDL fluent.
    @return Z3 variable name.
    """
    return str(fluent).split('_$')[0].replace('Not(','').replace('))',')')

def getZ3Effect(root, z3_variable, step, numeric_constants):
    z3effect = inorderTraverseRHDEffect(root, z3_variable, step, numeric_constants)
    return (getZ3VariableName(z3effect), z3effect)

def getArithBoolExprs(root, z3_variable, step, numeric_constants):

    arith_ret_list = []
    bool_ret_list = []
    arit_subgoals, bool_subgoals = inorderTraverseRHDEffect(root, z3_variable, step, numeric_constants)

    # there is no clean way to know where this ele is a boolean or arithmetic expression.
    for ele in root:
        z3_ele = inorderTraverseRHDEffect(ele, z3_variable, step, numeric_constants)
        for arith_subgoal in arit_subgoals:
            try:
                if z3_ele == arith_subgoal:
                    arith_ret_list.append((getZ3VariableName(ele.fluent), arith_subgoal))
                    break
            except:
                break
        for bool_subgoal in bool_subgoals:
            try:
                if z3_ele == bool_subgoal:
                    bool_ret_list.append((getZ3VariableName(ele.fluent), bool_subgoal))
                    break
            except:
                break

    return arith_ret_list, bool_ret_list
    return inorderTraverseRHDEffect(root, z3_variable, step, numeric_constants)

def inorderTraverseRHDEffect(root, z3_variable, step, numeric_constants):
    #if root is None,return
    if isinstance(root, list):
        subgoals = []
        arithmetic_subgoals = []
        boolean_subgoals = []

        for subgoal in root:
            _subgoal = inorderTraverseRHDEffect(subgoal, z3_variable, step, numeric_constants)
            if z3.is_bool(_subgoal):
                boolean_subgoals.append(_subgoal)
            else:
                arithmetic_subgoals.append(_subgoal)
            subgoals.append(_subgoal)
        return arithmetic_subgoals, boolean_subgoals
        
    elif isinstance(root, unified_planning.model.effect.Effect):
        if root.kind in [EffectKind.INCREASE, EffectKind.DECREASE, EffectKind.ASSIGN]:
            operand_1 = inorderTraverse(root.fluent, z3_variable, step, numeric_constants)
            operand_2 = inorderTraverse(root.value,  z3_variable, step, numeric_constants)
            if root.kind == EffectKind.INCREASE:
                #self.numeric_variables[step+1][fluent_name] == self.numeric_variables[step][fluent_name] + add_var))
                return operand_1 + operand_2
            elif root.kind == EffectKind.DECREASE:
                return operand_1 - operand_2
            elif root.kind == EffectKind.ASSIGN:
                var = inorderTraverse(root.fluent, z3_variable, step, numeric_constants)
                # Check the var type if it is boolean or numeric
                if z3.is_bool(var):
                    return var if root.value.is_true() else z3.Not(var)
                # There is a bug here.
                value = inorderTraverse(root.value, z3_variable, step, numeric_constants)
                return value
    elif isinstance(root, unified_planning.model.fnode.FNode):
        return inorderTraverse(root, z3_variable, step, numeric_constants)
    else:
        raise Exception('Unknown type for effect')

def inorderTraverse(root, z3_variable, step, numeric_constants, z3_touched_variables = None):
    #if root is None,return
    if isinstance(root, list):
        subgoals = []
        for subgoal in root:
            subgoals.append(inorderTraverse(subgoal, z3_variable, step, numeric_constants, z3_touched_variables))
        if root[0].node_type == OperatorKind.OR:
            return z3.Or(subgoals) if len(subgoals) > 1 else subgoals[0]
        else:
            return z3.And(subgoals) if len(subgoals) > 1 else subgoals[0]
    elif isinstance(root, unified_planning.model.effect.Effect):
        if root.kind in [EffectKind.INCREASE, EffectKind.DECREASE, EffectKind.ASSIGN]:
            operand_1 = inorderTraverse(root.fluent, z3_variable, step, numeric_constants, z3_touched_variables)
            operand_2 = inorderTraverse(root.value,  z3_variable, step, numeric_constants, z3_touched_variables)
            if root.kind == EffectKind.INCREASE:
                #self.numeric_variables[step+1][fluent_name] == self.numeric_variables[step][fluent_name] + add_var))
                return z3_variable[step+1][str(root.fluent)] == operand_1 + operand_2
            elif root.kind == EffectKind.DECREASE:
                return z3_variable[step+1][str(root.fluent)] == operand_1 - operand_2
            elif root.kind == EffectKind.ASSIGN:
                var = inorderTraverse(root.fluent, z3_variable, step+1, numeric_constants, z3_touched_variables)
                # Check the var type if it is boolean or numeric
                if z3.is_bool(var):
                    return var if root.value.is_true() else z3.Not(var)
                value = inorderTraverse(root.value, z3_variable, step, numeric_constants, z3_touched_variables)
                return z3_variable[step+1][str(root.fluent)] == value
    elif isinstance(root, unified_planning.model.fnode.FNode):
        if root.node_type in [OperatorKind.AND, OperatorKind.OR]:
            operands = []
            for arg in root.args:
                if z3_touched_variables is not None:
                    subgoal_z3 = inorderTraverse(arg, z3_variable, step, numeric_constants, z3_touched_variables)
                    touched_variables = []
                    for sg_fluent in FreeVarsExtractor().get(arg):
                        if str(sg_fluent) in z3_touched_variables:
                            touched_variables.append(z3_touched_variables[str(sg_fluent)])
                    operands.append(z3.Or(subgoal_z3, z3.Or(touched_variables) if len(touched_variables) > 1 else touched_variables[0]))
                else:
                    operands.append(inorderTraverse(arg, z3_variable, step, numeric_constants, z3_touched_variables))
            if root.node_type == OperatorKind.OR:
                return z3.Or(operands)
            else:
                return z3.And(operands)
        elif root.node_type == OperatorKind.EQUALS:
            operand_1 = inorderTraverse(root.args[0], z3_variable, step, numeric_constants, z3_touched_variables)
            operand_2 = inorderTraverse(root.args[1], z3_variable, step, numeric_constants, z3_touched_variables)
            return operand_1 - operand_2 == z3.RealVal(0)
        elif root.node_type in IRA_RELATIONS:
            operand_1 = inorderTraverse(root.args[0], z3_variable, step, numeric_constants, z3_touched_variables)
            operand_2 = inorderTraverse(root.args[1], z3_variable, step, numeric_constants, z3_touched_variables)

            if root.node_type == OperatorKind.LE:
                return operand_1 <= operand_2
            elif root.node_type == OperatorKind.LT:
                return operand_1 < operand_2
            else:
                raise Exception("Unknown relation {}".format(root.node_type))
        elif root.node_type in IRA_OPERATORS:
            operands = []
            for arg in root.args:
                operands.append(inorderTraverse(arg, z3_variable, step, numeric_constants, z3_touched_variables))
            if root.node_type == OperatorKind.PLUS:
                expression = operands[0] + operands[1]
                for i in range(2, len(operands)):
                    expression += operands[i]
            elif root.node_type == OperatorKind.MINUS:
                expression = operands[0] - operands[1]
                for i in range(2, len(operands)):
                    expression -= operands[i]
            elif root.node_type == OperatorKind.TIMES:
                expression = operands[0] * operands[1]
                for i in range(2, len(operands)):
                    expression *= operands[i]
            elif root.node_type == OperatorKind.DIV:
                expression = operands[0] / operands[1]
                for i in range(2, len(operands)):
                    expression /= operands[i]
            else:
                raise Exception("Unknown operator {}".format(root.node_type))
            return expression
        # these two should be retreived from the elements we already computed.
        elif root.node_type == OperatorKind.NOT:
            if root.args[0].node_type == OperatorKind.FLUENT_EXP:
                return z3.Not(z3_variable[step][str(root.args[0])])
            else:
                return z3.Not(inorderTraverse(root.args[0], z3_variable, step, numeric_constants, z3_touched_variables))
        elif root.node_type in [OperatorKind.BOOL_CONSTANT, OperatorKind.FLUENT_EXP]:
            if str(root) in list(numeric_constants.keys()):
                return z3.RealVal(numeric_constants[str(root)])
            elif root.node_type == OperatorKind.BOOL_CONSTANT:
                return z3.BoolVal(root)
            else:
                return z3_variable[step][str(root)]
        elif root.node_type in [OperatorKind.INT_CONSTANT, OperatorKind.REAL_CONSTANT]:
            return z3.RealVal(root)
        else:
            raise Exception("Unknown operator {}".format(root.node_type))
    else:
        raise Exception("Unknown operator {}".format(root.node_type))

def msgprint(msg, verbose=True):
    if verbose:
        print(msg)