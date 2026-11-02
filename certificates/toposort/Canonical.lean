import Aesop
import Lean.Elab.Tactic.Omega
import ToposortSort.Spec.Toposort
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_toposort_empty : spec_toposort_empty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_toposort_empty, canonical, Toposort.toposort, Toposort.toposort_flatten]
  | solve | unfold spec_toposort_empty; dsimp [canonical]; aesop
  | solve | unfold spec_toposort_empty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_toposort_empty
