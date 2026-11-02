import Aesop
import Lean.Elab.Tactic.Omega
import Ntheory.Spec.Residue
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_jacobi_base : spec_jacobi_base canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_jacobi_base, canonical, Ntheory.discreteLog, Ntheory.isQuadraticResidue, Ntheory.jacobiSymbol, Ntheory.legendreSymbol, Ntheory.nOrder, Ntheory.nthrootMod, Ntheory.sqrtMod, Ntheory.totient]
  | solve | unfold spec_jacobi_base; dsimp [canonical]; aesop
  | solve | unfold spec_jacobi_base; dsimp [canonical]; intros; omega

#print axioms canonical_spec_jacobi_base

theorem canonical_spec_totient_one : spec_totient_one canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_totient_one, canonical, Ntheory.discreteLog, Ntheory.isQuadraticResidue, Ntheory.jacobiSymbol, Ntheory.legendreSymbol, Ntheory.nOrder, Ntheory.nthrootMod, Ntheory.sqrtMod, Ntheory.totient]
  | solve | unfold spec_totient_one; dsimp [canonical]; aesop
  | solve | unfold spec_totient_one; dsimp [canonical]; intros; omega

#print axioms canonical_spec_totient_one
