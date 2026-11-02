import Aesop
import Lean.Elab.Tactic.Omega
import Dijkstar.Spec.ShortestPath
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_none_iff_unreachable : spec_none_iff_unreachable canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_none_iff_unreachable, canonical, Dijkstar.edgeWeight, Dijkstar.findPathCost, Dijkstar.reachable]
  | solve | unfold spec_none_iff_unreachable; dsimp [canonical]; aesop
  | solve | unfold spec_none_iff_unreachable; dsimp [canonical]; intros; omega

#print axioms canonical_spec_none_iff_unreachable
