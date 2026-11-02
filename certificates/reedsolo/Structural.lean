import Reedsolo.Spec.Field
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_gf_mul_carryless_anchored : spec_gf_mul_carryless_anchored canonical := by
  unfold spec_gf_mul_carryless_anchored
  intros
  rfl

#print axioms structural_spec_gf_mul_carryless_anchored

theorem structural_spec_gf_pow_zero : spec_gf_pow_zero canonical := by
  unfold spec_gf_pow_zero
  intros
  rfl

#print axioms structural_spec_gf_pow_zero
