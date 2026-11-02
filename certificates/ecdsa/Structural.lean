import Ecdsa.Spec.Curve
import Ecdsa.Spec.Modular
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_jacobi_denom_one : spec_jacobi_denom_one canonical := by
  unfold spec_jacobi_denom_one
  intros
  rfl

#print axioms structural_spec_jacobi_denom_one

theorem structural_spec_contains_point_infinity : spec_contains_point_infinity canonical := by
  unfold spec_contains_point_infinity
  intros
  rfl

#print axioms structural_spec_contains_point_infinity

theorem structural_spec_point_double_at_infinity : spec_point_double_at_infinity canonical := by
  unfold spec_point_double_at_infinity
  intros
  rfl

#print axioms structural_spec_point_double_at_infinity

theorem structural_spec_point_add_left_identity : spec_point_add_left_identity canonical := by
  unfold spec_point_add_left_identity
  intros
  rfl

#print axioms structural_spec_point_add_left_identity

theorem structural_spec_scalar_mult_zero : spec_scalar_mult_zero canonical := by
  unfold spec_scalar_mult_zero
  intros
  rfl

#print axioms structural_spec_scalar_mult_zero

theorem structural_spec_scalar_mult_succ : spec_scalar_mult_succ canonical := by
  unfold spec_scalar_mult_succ
  intros
  rfl

#print axioms structural_spec_scalar_mult_succ

theorem structural_spec_scalar_mult_one : spec_scalar_mult_one canonical := by
  unfold spec_scalar_mult_one
  intros
  rfl

#print axioms structural_spec_scalar_mult_one
