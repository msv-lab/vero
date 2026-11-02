import Aesop
import Lean.Elab.Tactic.Omega
import Difflib.Spec.SequenceMatcher
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_matchSize_correct : spec_matchSize_correct canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_matchSize_correct, canonical, Difflib.findLongestMatch, Difflib.getMatchingBlocks, Difflib.matchSize]
  | solve | unfold spec_matchSize_correct; dsimp [canonical]; aesop
  | solve | unfold spec_matchSize_correct; dsimp [canonical]; intros; omega

#print axioms canonical_spec_matchSize_correct

theorem canonical_spec_gmb_sentinel : spec_gmb_sentinel canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_gmb_sentinel, canonical, Difflib.findLongestMatch, Difflib.getMatchingBlocks, Difflib.matchSize]
  | solve | unfold spec_gmb_sentinel; dsimp [canonical]; aesop
  | solve | unfold spec_gmb_sentinel; dsimp [canonical]; intros; omega

#print axioms canonical_spec_gmb_sentinel

theorem canonical_spec_gmb_nonempty : spec_gmb_nonempty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_gmb_nonempty, canonical, Difflib.findLongestMatch, Difflib.getMatchingBlocks, Difflib.matchSize]
  | solve | unfold spec_gmb_nonempty; dsimp [canonical]; aesop
  | solve | unfold spec_gmb_nonempty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_gmb_nonempty

theorem canonical_spec_gmb_empty : spec_gmb_empty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_gmb_empty, canonical, Difflib.findLongestMatch, Difflib.getMatchingBlocks, Difflib.matchSize]
  | solve | unfold spec_gmb_empty; dsimp [canonical]; aesop
  | solve | unfold spec_gmb_empty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_gmb_empty
