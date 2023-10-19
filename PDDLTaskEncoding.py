
from unified_planning.io import PDDLReader
from unified_planning.shortcuts import *

from pddlencodings.linear import LinearEncoding
from pddlencodings.r2e import R2EEncoding

from utilities import ExtractPlan

__version__ = "0.0.1"

_encodingModels = {
    'linear': LinearEncoding,
    'r2e': R2EEncoding
}

def encodeProblem(domainFile, problemFile, encodingModel, encodingOptions):
    if encodingModel not in _encodingModels:
        raise ValueError('Encoding model {} not supported.'.format(encodingModel))
    up.shortcuts.get_environment().credits_stream = None
    return _encodingModels[encodingModel](PDDLReader().parse_problem(domainFile, problemFile), encodingOptions)

def extractPlanFromModel(solver, encoder, horizon, objective=None):
    return ExtractPlan.ExtractPlan(solver, encoder, horizon, objective)

__all__ = ['encodeProblem', 'extractPlanFromModel']