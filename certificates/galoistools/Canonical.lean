import Aesop
import Lean.Elab.Tactic.Omega
import Galoistools.Spec.Division
import Galoistools.Spec.Ring
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_mul_zero : spec_mul_zero canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_mul_zero, canonical, Galoistools.gfAdd, Galoistools.gfDiv, Galoistools.gfGcd, Galoistools.gfGcdex, Galoistools.gfMonic, Galoistools.gfMul, Galoistools.gfNeg, Galoistools.gfPowMod, Galoistools.gfQuo, Galoistools.gfRem, Galoistools.gfSub]
  | solve | unfold spec_mul_zero; dsimp [canonical]; aesop
  | solve | unfold spec_mul_zero; dsimp [canonical]; intros; omega

#print axioms canonical_spec_mul_zero

theorem canonical_spec_powmod_zero : spec_powmod_zero canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_powmod_zero, canonical, Galoistools.gfAdd, Galoistools.gfDiv, Galoistools.gfGcd, Galoistools.gfGcdex, Galoistools.gfMonic, Galoistools.gfMul, Galoistools.gfNeg, Galoistools.gfPowMod, Galoistools.gfQuo, Galoistools.gfRem, Galoistools.gfSub]
  | solve | unfold spec_powmod_zero; dsimp [canonical]; aesop
  | solve | unfold spec_powmod_zero; dsimp [canonical]; intros; omega

#print axioms canonical_spec_powmod_zero

theorem canonical_spec_gcdex_both_empty : spec_gcdex_both_empty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_gcdex_both_empty, canonical, Galoistools.gfAdd, Galoistools.gfDiv, Galoistools.gfGcd, Galoistools.gfGcdex, Galoistools.gfMonic, Galoistools.gfMul, Galoistools.gfNeg, Galoistools.gfPowMod, Galoistools.gfQuo, Galoistools.gfRem, Galoistools.gfSub]
  | solve | unfold spec_gcdex_both_empty; dsimp [canonical]; aesop
  | solve | unfold spec_gcdex_both_empty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_gcdex_both_empty
