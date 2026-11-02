import Aesop
import Lean.Elab.Tactic.Omega
import VerifiedBitmasks.Spec.BitmaskArray
import VerifiedBitmasks.Spec.BitmaskIF
import VerifiedBitmasks.Spec.BitmaskImplIF
import VerifiedBitmasks.Spec.BitmaskSeq
import VerifiedBitmasks.Spec.MachineWords
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_bitwise_mask_is_ones : spec_bitwise_mask_is_ones canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_bitwise_mask_is_ones, canonical, VerifiedBitmasks.bIF_and, VerifiedBitmasks.bIF_clearBit, VerifiedBitmasks.bIF_concat, VerifiedBitmasks.bIF_getBit, VerifiedBitmasks.bIF_nbits, VerifiedBitmasks.bIF_newOnes, VerifiedBitmasks.bIF_newZeros, VerifiedBitmasks.bIF_not, VerifiedBitmasks.bIF_or, VerifiedBitmasks.bIF_popcnt, VerifiedBitmasks.bIF_setBit, VerifiedBitmasks.bIF_split, VerifiedBitmasks.bIF_toggleBit, VerifiedBitmasks.bIF_xor, VerifiedBitmasks.bSeq_and, VerifiedBitmasks.bSeq_cNewOnes, VerifiedBitmasks.bSeq_cNewZeros, VerifiedBitmasks.bSeq_clearBit, VerifiedBitmasks.bSeq_eq, VerifiedBitmasks.bSeq_getBit, VerifiedBitmasks.bSeq_isOnes, VerifiedBitmasks.bSeq_isZeros, VerifiedBitmasks.bSeq_nbits, VerifiedBitmasks.bSeq_not, VerifiedBitmasks.bSeq_or, VerifiedBitmasks.bSeq_popcnt, VerifiedBitmasks.bSeq_setBit, VerifiedBitmasks.bSeq_toggleBit, VerifiedBitmasks.bSeq_xor, VerifiedBitmasks.bitwiseAdd, VerifiedBitmasks.bitwiseAnd, VerifiedBitmasks.bitwiseBit, VerifiedBitmasks.bitwiseClearBit, VerifiedBitmasks.bitwiseComp, VerifiedBitmasks.bitwiseDiv, VerifiedBitmasks.bitwiseGetBit, VerifiedBitmasks.bitwiseLeftShift, VerifiedBitmasks.bitwiseMask, VerifiedBitmasks.bitwiseMod, VerifiedBitmasks.bitwiseMul, VerifiedBitmasks.bitwiseNot, VerifiedBitmasks.bitwiseOnes, VerifiedBitmasks.bitwiseOr, VerifiedBitmasks.bitwiseRightShift, VerifiedBitmasks.bitwiseSetBit, VerifiedBitmasks.bitwiseSub, VerifiedBitmasks.bitwiseToggleBit, VerifiedBitmasks.bitwiseXor, VerifiedBitmasks.bitwiseZeros, bArr_and, bArr_cNewOnes, bArr_cNewZeros, bArr_clearBit, bArr_eq, bArr_getBit, bArr_isOnes, bArr_isZeros, bArr_nbits, bArr_not, bArr_or, bArr_popcnt, bArr_setBit, bArr_toggleBit, bArr_xor, bFC_and, bFC_clearBit, bFC_getBit, bFC_nbits, bFC_newOnes, bFC_newZeros, bFC_not, bFC_or, bFC_popcnt, bFC_setBit, bFC_toggleBit, bFC_xor, bIIF_and, bIIF_clearBit, bIIF_getBit, bIIF_nbits, bIIF_newOnes, bIIF_newZeros, bIIF_not, bIIF_or, bIIF_popcnt, bIIF_setBit, bIIF_toggleBit, bIIF_xor]
  | solve | unfold spec_bitwise_mask_is_ones; dsimp [canonical]; aesop
  | solve | unfold spec_bitwise_mask_is_ones; dsimp [canonical]; intros; omega

#print axioms canonical_spec_bitwise_mask_is_ones

theorem canonical_spec_bitwise_mask_is_zeros : spec_bitwise_mask_is_zeros canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_bitwise_mask_is_zeros, canonical, VerifiedBitmasks.bIF_and, VerifiedBitmasks.bIF_clearBit, VerifiedBitmasks.bIF_concat, VerifiedBitmasks.bIF_getBit, VerifiedBitmasks.bIF_nbits, VerifiedBitmasks.bIF_newOnes, VerifiedBitmasks.bIF_newZeros, VerifiedBitmasks.bIF_not, VerifiedBitmasks.bIF_or, VerifiedBitmasks.bIF_popcnt, VerifiedBitmasks.bIF_setBit, VerifiedBitmasks.bIF_split, VerifiedBitmasks.bIF_toggleBit, VerifiedBitmasks.bIF_xor, VerifiedBitmasks.bSeq_and, VerifiedBitmasks.bSeq_cNewOnes, VerifiedBitmasks.bSeq_cNewZeros, VerifiedBitmasks.bSeq_clearBit, VerifiedBitmasks.bSeq_eq, VerifiedBitmasks.bSeq_getBit, VerifiedBitmasks.bSeq_isOnes, VerifiedBitmasks.bSeq_isZeros, VerifiedBitmasks.bSeq_nbits, VerifiedBitmasks.bSeq_not, VerifiedBitmasks.bSeq_or, VerifiedBitmasks.bSeq_popcnt, VerifiedBitmasks.bSeq_setBit, VerifiedBitmasks.bSeq_toggleBit, VerifiedBitmasks.bSeq_xor, VerifiedBitmasks.bitwiseAdd, VerifiedBitmasks.bitwiseAnd, VerifiedBitmasks.bitwiseBit, VerifiedBitmasks.bitwiseClearBit, VerifiedBitmasks.bitwiseComp, VerifiedBitmasks.bitwiseDiv, VerifiedBitmasks.bitwiseGetBit, VerifiedBitmasks.bitwiseLeftShift, VerifiedBitmasks.bitwiseMask, VerifiedBitmasks.bitwiseMod, VerifiedBitmasks.bitwiseMul, VerifiedBitmasks.bitwiseNot, VerifiedBitmasks.bitwiseOnes, VerifiedBitmasks.bitwiseOr, VerifiedBitmasks.bitwiseRightShift, VerifiedBitmasks.bitwiseSetBit, VerifiedBitmasks.bitwiseSub, VerifiedBitmasks.bitwiseToggleBit, VerifiedBitmasks.bitwiseXor, VerifiedBitmasks.bitwiseZeros, bArr_and, bArr_cNewOnes, bArr_cNewZeros, bArr_clearBit, bArr_eq, bArr_getBit, bArr_isOnes, bArr_isZeros, bArr_nbits, bArr_not, bArr_or, bArr_popcnt, bArr_setBit, bArr_toggleBit, bArr_xor, bFC_and, bFC_clearBit, bFC_getBit, bFC_nbits, bFC_newOnes, bFC_newZeros, bFC_not, bFC_or, bFC_popcnt, bFC_setBit, bFC_toggleBit, bFC_xor, bIIF_and, bIIF_clearBit, bIIF_getBit, bIIF_nbits, bIIF_newOnes, bIIF_newZeros, bIIF_not, bIIF_or, bIIF_popcnt, bIIF_setBit, bIIF_toggleBit, bIIF_xor]
  | solve | unfold spec_bitwise_mask_is_zeros; dsimp [canonical]; aesop
  | solve | unfold spec_bitwise_mask_is_zeros; dsimp [canonical]; intros; omega

#print axioms canonical_spec_bitwise_mask_is_zeros
