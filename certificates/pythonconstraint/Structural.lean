import Pythonconstraint.Spec.Csp
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_count_eq_length : spec_count_eq_length canonical := by
  unfold spec_count_eq_length
  intros
  rfl

#print axioms structural_spec_count_eq_length
