import Aesop
import Lean.Elab.Tactic.Omega
import PackagingVersion.Spec.Version
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_sort_nil : spec_sort_nil canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_sort_nil, canonical, PackagingVersion.maxVer, PackagingVersion.minVer, PackagingVersion.sortVers, PackagingVersion.verEq, PackagingVersion.verLe]
  | solve | unfold spec_sort_nil; dsimp [canonical]; aesop
  | solve | unfold spec_sort_nil; dsimp [canonical]; intros; omega

#print axioms canonical_spec_sort_nil
