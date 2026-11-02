import Aesop
import Lean.Elab.Tactic.Omega
import SortedcontainersCore.Spec.SortedDict
import SortedcontainersCore.Spec.SortedList
import SortedcontainersCore.Spec.SortedSet
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_sortedDict_reversed_eq_keysRev : spec_sortedDict_reversed_eq_keysRev canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_sortedDict_reversed_eq_keysRev, canonical]
  | solve | unfold spec_sortedDict_reversed_eq_keysRev; dsimp [canonical]; aesop
  | solve | unfold spec_sortedDict_reversed_eq_keysRev; dsimp [canonical]; intros; omega

#print axioms canonical_spec_sortedDict_reversed_eq_keysRev

theorem canonical_spec_sortedDict_keys_eq_itemsFirst : spec_sortedDict_keys_eq_itemsFirst canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_sortedDict_keys_eq_itemsFirst, canonical]
  | solve | unfold spec_sortedDict_keys_eq_itemsFirst; dsimp [canonical]; aesop
  | solve | unfold spec_sortedDict_keys_eq_itemsFirst; dsimp [canonical]; intros; omega

#print axioms canonical_spec_sortedDict_keys_eq_itemsFirst

theorem canonical_spec_sortedDict_values_eq_itemsSecond : spec_sortedDict_values_eq_itemsSecond canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_sortedDict_values_eq_itemsSecond, canonical]
  | solve | unfold spec_sortedDict_values_eq_itemsSecond; dsimp [canonical]; aesop
  | solve | unfold spec_sortedDict_values_eq_itemsSecond; dsimp [canonical]; intros; omega

#print axioms canonical_spec_sortedDict_values_eq_itemsSecond
