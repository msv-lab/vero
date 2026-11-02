import VestV2.Spec.BitcoinVarint
import VestV2.Spec.Errors
import VestV2.Spec.RegularBytes
import VestV2.Spec.RegularClone
import VestV2.Spec.RegularEnd
import VestV2.Spec.RegularFail
import VestV2.Spec.RegularLeb128
import VestV2.Spec.RegularModifier
import VestV2.Spec.RegularSuccess
import VestV2.Spec.RegularTag
import VestV2.Spec.RegularUints
import VestV2.Spec.RegularVariant
import VestV2.Spec.Utils
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_from_parse_error_correct : spec_from_parse_error_correct canonical := by
  unfold spec_from_parse_error_correct
  intros
  rfl

#print axioms structural_spec_from_parse_error_correct

theorem structural_spec_from_serialize_error_correct : spec_from_serialize_error_correct canonical := by
  unfold spec_from_serialize_error_correct
  intros
  rfl

#print axioms structural_spec_from_serialize_error_correct

theorem structural_spec_set_range_correct : spec_set_range_correct canonical := by
  unfold spec_set_range_correct
  intros
  rfl

#print axioms structural_spec_set_range_correct

theorem structural_spec_compare_slice_correct : spec_compare_slice_correct canonical := by
  unfold spec_compare_slice_correct
  intros
  rfl

#print axioms structural_spec_compare_slice_correct

theorem structural_spec_tail_parse_correct : spec_tail_parse_correct canonical := by
  unfold spec_tail_parse_correct
  intros
  rfl

#print axioms structural_spec_tail_parse_correct

theorem structural_spec_end_serialize_zero : spec_end_serialize_zero canonical := by
  unfold spec_end_serialize_zero
  intros
  rfl

#print axioms structural_spec_end_serialize_zero

theorem structural_spec_success_always_succeeds : spec_success_always_succeeds canonical := by
  unfold spec_success_always_succeeds
  intros
  rfl

#print axioms structural_spec_success_always_succeeds

theorem structural_spec_success_serialize_zero : spec_success_serialize_zero canonical := by
  unfold spec_success_serialize_zero
  intros
  rfl

#print axioms structural_spec_success_serialize_zero

theorem structural_spec_u8_roundtrip : spec_u8_roundtrip canonical := by
  unfold spec_u8_roundtrip
  intros
  rfl

#print axioms structural_spec_u8_roundtrip
