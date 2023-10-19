
from z3 import *
from unified_planning.shortcuts import *
from unified_planning.plans import SequentialPlan
from unified_planning.plans import ActionInstance
from unified_planning.engines.compilers.utils import *
from unified_planning.engines.results import *

class ExtractPlan:
    def __init__(self, solver, encoder, horizon, objective=None):

        self.horizon     = horizon
        self.plan_z3     = []
        self._liftedPlan = []
        
        # for numeric problems, it uses the gounrder to generating groudned actions and this cannot be cloned.
        self.encoder     = encoder

        if solver is None:
            # Return an empty plan
            self.plan = SequentialPlan([])
            self._is_valid   = None
        else: 
            self.plan        = self._extractPlan(solver)
            self.cost        = self._extractCost(objective)
            self._is_valid = self._validate() 
            if not self.is_valid():
                self.plan = SequentialPlan([])
            
    def _extractPlan(self, solver):
        plan = []
        model = solver.model()
        ## linearize partial-order plan
        for step in range(self.horizon):
            for action in self.encoder.getActionsList():
                if is_true(model[self.encoder.getAction(step, action.name)]):    
                    plan.append(ActionInstance(action))
                    self._liftedPlan.append(self.encoder.grounding_results.map_back_action_instance(ActionInstance(action))) 
                    self.plan_z3.append(self.encoder.getAction(step, action.name))
        return SequentialPlan(plan, self.encoder.getGroundedProblem().environment) 

    def __len__(self):
        return len(self.plan.actions)

    def _extractCost(self, objective=None):
        return objective.value() if objective else len(self.plan.actions)

    def _validate(self):
        with PlanValidator(problem_kind=self.encoder.getGroundedProblem().kind, plan_kind=self.plan.kind) as validator:
            return validator.validate(self.encoder.getGroundedProblem(), self.plan)

    def is_valid(self):
        return self._is_valid.status.value == 1 if self._is_valid else False

    def getLiftedPlan(self):
        return self._liftedPlan

    def getZ3Actions(self):
        return self.plan_z3