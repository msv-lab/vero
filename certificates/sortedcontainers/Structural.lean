import SortedcontainersCore.Spec.SortedDict
import SortedcontainersCore.Spec.SortedList
import SortedcontainersCore.Spec.SortedSet
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_sortedList_remove_eq_discard : spec_sortedList_remove_eq_discard canonical := by
  unfold spec_sortedList_remove_eq_discard
  intros
  rfl

#print axioms structural_spec_sortedList_remove_eq_discard

theorem structural_spec_sortedKeyList_remove_eq_discard : spec_sortedKeyList_remove_eq_discard canonical := by
  unfold spec_sortedKeyList_remove_eq_discard
  intros
  rfl

#print axioms structural_spec_sortedKeyList_remove_eq_discard

theorem structural_spec_sortedSet_count_contains_law : spec_sortedSet_count_contains_law canonical := by
  unfold spec_sortedSet_count_contains_law
  intros
  rfl

#print axioms structural_spec_sortedSet_count_contains_law

theorem structural_spec_sortedSet_remove_eq_discard : spec_sortedSet_remove_eq_discard canonical := by
  unfold spec_sortedSet_remove_eq_discard
  intros
  rfl

#print axioms structural_spec_sortedSet_remove_eq_discard

theorem structural_spec_sortedDict_keys_agree_with_items : spec_sortedDict_keys_agree_with_items canonical := by
  unfold spec_sortedDict_keys_agree_with_items
  intros
  rfl

#print axioms structural_spec_sortedDict_keys_agree_with_items
