import Galoistools.Spec.Division
import Galoistools.Spec.Ring
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_rem_is_div_snd : spec_rem_is_div_snd canonical := by
  unfold spec_rem_is_div_snd
  intros
  rfl

#print axioms structural_spec_rem_is_div_snd

theorem structural_spec_quo_is_div_fst : spec_quo_is_div_fst canonical := by
  unfold spec_quo_is_div_fst
  intros
  rfl

#print axioms structural_spec_quo_is_div_fst

theorem structural_spec_gcd_zero_right : spec_gcd_zero_right canonical := by
  unfold spec_gcd_zero_right
  intros
  rfl

#print axioms structural_spec_gcd_zero_right
