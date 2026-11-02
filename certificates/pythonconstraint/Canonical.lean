import Aesop
import Lean.Elab.Tactic.Omega
import Pythonconstraint.Spec.Csp
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_no_variables_empty : spec_no_variables_empty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_no_variables_empty, canonical, Pythonconstraint.getSolution, Pythonconstraint.getSolutions, Pythonconstraint.holds, Pythonconstraint.solutionCount]
  | solve | unfold spec_no_variables_empty; dsimp [canonical]; aesop
  | solve | unfold spec_no_variables_empty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_no_variables_empty
