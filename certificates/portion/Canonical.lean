import Aesop
import Lean.Elab.Tactic.Omega
import Portion.Spec.Algebra
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_complement_involutive : spec_complement_involutive canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_complement_involutive, canonical, Portion.complement, Portion.contains, Portion.difference, Portion.intersection, Portion.isEmpty, Portion.union]
  | solve | unfold spec_complement_involutive; dsimp [canonical]; aesop
  | solve | unfold spec_complement_involutive; dsimp [canonical]; intros; omega

#print axioms canonical_spec_complement_involutive

theorem canonical_spec_complement_complement_eq : spec_complement_complement_eq canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_complement_complement_eq, canonical, Portion.complement, Portion.contains, Portion.difference, Portion.intersection, Portion.isEmpty, Portion.union]
  | solve | unfold spec_complement_complement_eq; dsimp [canonical]; aesop
  | solve | unfold spec_complement_complement_eq; dsimp [canonical]; intros; omega

#print axioms canonical_spec_complement_complement_eq
