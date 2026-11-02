import Portion.Spec.Algebra
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_contains_correct : spec_contains_correct canonical := by
  unfold spec_contains_correct
  intros
  rfl

#print axioms structural_spec_contains_correct
