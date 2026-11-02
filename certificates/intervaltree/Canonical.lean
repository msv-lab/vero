import Aesop
import Lean.Elab.Tactic.Omega
import Intervaltree.Spec.Merge
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_overlaps_self_nonempty : spec_overlaps_self_nonempty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_overlaps_self_nonempty, canonical, Intervaltree.chop, Intervaltree.mergeOverlaps, Intervaltree.overlaps]
  | solve | unfold spec_overlaps_self_nonempty; dsimp [canonical]; aesop
  | solve | unfold spec_overlaps_self_nonempty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_overlaps_self_nonempty

theorem canonical_spec_overlaps_self_empty : spec_overlaps_self_empty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_overlaps_self_empty, canonical, Intervaltree.chop, Intervaltree.mergeOverlaps, Intervaltree.overlaps]
  | solve | unfold spec_overlaps_self_empty; dsimp [canonical]; aesop
  | solve | unfold spec_overlaps_self_empty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_overlaps_self_empty
