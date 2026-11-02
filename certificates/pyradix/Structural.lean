import Pyradix.Spec.Radix
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_covered_filter_eq : spec_covered_filter_eq canonical := by
  unfold spec_covered_filter_eq
  intros
  rfl

#print axioms structural_spec_covered_filter_eq
