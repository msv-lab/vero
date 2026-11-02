import Aesop
import Lean.Elab.Tactic.Omega
import Primepy.Spec.Primes
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_phi_counts_coprime_range : spec_phi_counts_coprime_range canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_phi_counts_coprime_range, canonical, Primepy.between, Primepy.check, Primepy.factor, Primepy.factors, Primepy.first, Primepy.phi, Primepy.upto]
  | solve | unfold spec_phi_counts_coprime_range; dsimp [canonical]; aesop
  | solve | unfold spec_phi_counts_coprime_range; dsimp [canonical]; intros; omega

#print axioms canonical_spec_phi_counts_coprime_range

theorem canonical_spec_between_agrees_with_upto : spec_between_agrees_with_upto canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_between_agrees_with_upto, canonical, Primepy.between, Primepy.check, Primepy.factor, Primepy.factors, Primepy.first, Primepy.phi, Primepy.upto]
  | solve | unfold spec_between_agrees_with_upto; dsimp [canonical]; aesop
  | solve | unfold spec_between_agrees_with_upto; dsimp [canonical]; intros; omega

#print axioms canonical_spec_between_agrees_with_upto
