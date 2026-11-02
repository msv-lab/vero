import VerifiedBitmasks.Spec.BitmaskArray
import VerifiedBitmasks.Spec.BitmaskIF
import VerifiedBitmasks.Spec.BitmaskImplIF
import VerifiedBitmasks.Spec.BitmaskSeq
import VerifiedBitmasks.Spec.MachineWords
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_bitwise_not_comp_eq : spec_bitwise_not_comp_eq canonical := by
  unfold spec_bitwise_not_comp_eq
  intros
  rfl

#print axioms structural_spec_bitwise_not_comp_eq

theorem structural_spec_bIIF_newZeros_correct : spec_bIIF_newZeros_correct canonical := by
  unfold spec_bIIF_newZeros_correct
  intros
  rfl

#print axioms structural_spec_bIIF_newZeros_correct

theorem structural_spec_bIIF_newOnes_correct : spec_bIIF_newOnes_correct canonical := by
  unfold spec_bIIF_newOnes_correct
  intros
  rfl

#print axioms structural_spec_bIIF_newOnes_correct

theorem structural_spec_bIIF_nbits_correct : spec_bIIF_nbits_correct canonical := by
  unfold spec_bIIF_nbits_correct
  intros
  rfl

#print axioms structural_spec_bIIF_nbits_correct

theorem structural_spec_bIIF_popcnt_correct : spec_bIIF_popcnt_correct canonical := by
  unfold spec_bIIF_popcnt_correct
  intros
  rfl

#print axioms structural_spec_bIIF_popcnt_correct

theorem structural_spec_bIIF_getBit_correct : spec_bIIF_getBit_correct canonical := by
  unfold spec_bIIF_getBit_correct
  intros
  rfl

#print axioms structural_spec_bIIF_getBit_correct

theorem structural_spec_bIIF_setBit_correct : spec_bIIF_setBit_correct canonical := by
  unfold spec_bIIF_setBit_correct
  intros
  rfl

#print axioms structural_spec_bIIF_setBit_correct

theorem structural_spec_bIIF_clearBit_correct : spec_bIIF_clearBit_correct canonical := by
  unfold spec_bIIF_clearBit_correct
  intros
  rfl

#print axioms structural_spec_bIIF_clearBit_correct

theorem structural_spec_bIIF_toggleBit_correct : spec_bIIF_toggleBit_correct canonical := by
  unfold spec_bIIF_toggleBit_correct
  intros
  rfl

#print axioms structural_spec_bIIF_toggleBit_correct

theorem structural_spec_bIIF_and_correct : spec_bIIF_and_correct canonical := by
  unfold spec_bIIF_and_correct
  intros
  rfl

#print axioms structural_spec_bIIF_and_correct

theorem structural_spec_bIIF_or_correct : spec_bIIF_or_correct canonical := by
  unfold spec_bIIF_or_correct
  intros
  rfl

#print axioms structural_spec_bIIF_or_correct

theorem structural_spec_bIIF_xor_correct : spec_bIIF_xor_correct canonical := by
  unfold spec_bIIF_xor_correct
  intros
  rfl

#print axioms structural_spec_bIIF_xor_correct

theorem structural_spec_bIIF_not_correct : spec_bIIF_not_correct canonical := by
  unfold spec_bIIF_not_correct
  intros
  rfl

#print axioms structural_spec_bIIF_not_correct

theorem structural_spec_bSeq_cNewZeros_correct : spec_bSeq_cNewZeros_correct canonical := by
  unfold spec_bSeq_cNewZeros_correct
  intros
  rfl

#print axioms structural_spec_bSeq_cNewZeros_correct

theorem structural_spec_bSeq_cNewOnes_correct : spec_bSeq_cNewOnes_correct canonical := by
  unfold spec_bSeq_cNewOnes_correct
  intros
  rfl

#print axioms structural_spec_bSeq_cNewOnes_correct

theorem structural_spec_bSeq_nbits_correct : spec_bSeq_nbits_correct canonical := by
  unfold spec_bSeq_nbits_correct
  intros
  rfl

#print axioms structural_spec_bSeq_nbits_correct

theorem structural_spec_bSeq_popcnt_correct : spec_bSeq_popcnt_correct canonical := by
  unfold spec_bSeq_popcnt_correct
  intros
  rfl

#print axioms structural_spec_bSeq_popcnt_correct

theorem structural_spec_bSeq_getBit_correct : spec_bSeq_getBit_correct canonical := by
  unfold spec_bSeq_getBit_correct
  intros
  rfl

#print axioms structural_spec_bSeq_getBit_correct

theorem structural_spec_bSeq_setBit_correct : spec_bSeq_setBit_correct canonical := by
  unfold spec_bSeq_setBit_correct
  intros
  rfl

#print axioms structural_spec_bSeq_setBit_correct

theorem structural_spec_bSeq_clearBit_correct : spec_bSeq_clearBit_correct canonical := by
  unfold spec_bSeq_clearBit_correct
  intros
  rfl

#print axioms structural_spec_bSeq_clearBit_correct

theorem structural_spec_bSeq_toggleBit_correct : spec_bSeq_toggleBit_correct canonical := by
  unfold spec_bSeq_toggleBit_correct
  intros
  rfl

#print axioms structural_spec_bSeq_toggleBit_correct

theorem structural_spec_bSeq_eq_correct : spec_bSeq_eq_correct canonical := by
  unfold spec_bSeq_eq_correct
  intros
  rfl

#print axioms structural_spec_bSeq_eq_correct

theorem structural_spec_bSeq_isZeros_correct : spec_bSeq_isZeros_correct canonical := by
  unfold spec_bSeq_isZeros_correct
  intros
  rfl

#print axioms structural_spec_bSeq_isZeros_correct

theorem structural_spec_bSeq_isOnes_correct : spec_bSeq_isOnes_correct canonical := by
  unfold spec_bSeq_isOnes_correct
  intros
  rfl

#print axioms structural_spec_bSeq_isOnes_correct

theorem structural_spec_bSeq_and_correct : spec_bSeq_and_correct canonical := by
  unfold spec_bSeq_and_correct
  intros
  rfl

#print axioms structural_spec_bSeq_and_correct

theorem structural_spec_bSeq_or_correct : spec_bSeq_or_correct canonical := by
  unfold spec_bSeq_or_correct
  intros
  rfl

#print axioms structural_spec_bSeq_or_correct

theorem structural_spec_bSeq_xor_correct : spec_bSeq_xor_correct canonical := by
  unfold spec_bSeq_xor_correct
  intros
  rfl

#print axioms structural_spec_bSeq_xor_correct

theorem structural_spec_bSeq_not_correct : spec_bSeq_not_correct canonical := by
  unfold spec_bSeq_not_correct
  intros
  rfl

#print axioms structural_spec_bSeq_not_correct

theorem structural_spec_bArr_cNewZeros_correct : spec_bArr_cNewZeros_correct canonical := by
  unfold spec_bArr_cNewZeros_correct
  intros
  rfl

#print axioms structural_spec_bArr_cNewZeros_correct

theorem structural_spec_bArr_cNewOnes_correct : spec_bArr_cNewOnes_correct canonical := by
  unfold spec_bArr_cNewOnes_correct
  intros
  rfl

#print axioms structural_spec_bArr_cNewOnes_correct
