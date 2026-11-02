import Aesop
import Lean.Elab.Tactic.Omega
import Semver.Spec.Version
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_satisfies_nil : spec_satisfies_nil canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_satisfies_nil, canonical, Semver.compareV, Semver.satisfies, Semver.select, Semver.versionEq, Semver.versionLt]
  | solve | unfold spec_satisfies_nil; dsimp [canonical]; aesop
  | solve | unfold spec_satisfies_nil; dsimp [canonical]; intros; omega

#print axioms canonical_spec_satisfies_nil

theorem canonical_spec_satisfies_conj : spec_satisfies_conj canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_satisfies_conj, canonical, Semver.compareV, Semver.satisfies, Semver.select, Semver.versionEq, Semver.versionLt]
  | solve | unfold spec_satisfies_conj; dsimp [canonical]; aesop
  | solve | unfold spec_satisfies_conj; dsimp [canonical]; intros; omega

#print axioms canonical_spec_satisfies_conj
