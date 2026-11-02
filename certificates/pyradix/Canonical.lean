import Aesop
import Lean.Elab.Tactic.Omega
import Pyradix.Spec.Radix
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_delete_searchExact_none : spec_delete_searchExact_none canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_delete_searchExact_none, canonical, Pyradix.add, Pyradix.covered, Pyradix.delete, Pyradix.searchBest, Pyradix.searchExact, Pyradix.searchWorst]
  | solve | unfold spec_delete_searchExact_none; dsimp [canonical]; aesop
  | solve | unfold spec_delete_searchExact_none; dsimp [canonical]; intros; omega

#print axioms canonical_spec_delete_searchExact_none

theorem canonical_spec_covered_append : spec_covered_append canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_covered_append, canonical, Pyradix.add, Pyradix.covered, Pyradix.delete, Pyradix.searchBest, Pyradix.searchExact, Pyradix.searchWorst]
  | solve | unfold spec_covered_append; dsimp [canonical]; aesop
  | solve | unfold spec_covered_append; dsimp [canonical]; intros; omega

#print axioms canonical_spec_covered_append

theorem canonical_spec_searchBest_empty : spec_searchBest_empty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_searchBest_empty, canonical, Pyradix.add, Pyradix.covered, Pyradix.delete, Pyradix.searchBest, Pyradix.searchExact, Pyradix.searchWorst]
  | solve | unfold spec_searchBest_empty; dsimp [canonical]; aesop
  | solve | unfold spec_searchBest_empty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_searchBest_empty

theorem canonical_spec_delete_sublist : spec_delete_sublist canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_delete_sublist, canonical, Pyradix.add, Pyradix.covered, Pyradix.delete, Pyradix.searchBest, Pyradix.searchExact, Pyradix.searchWorst]
  | solve | unfold spec_delete_sublist; dsimp [canonical]; aesop
  | solve | unfold spec_delete_sublist; dsimp [canonical]; intros; omega

#print axioms canonical_spec_delete_sublist
