import LinkedList.Spec.CircularLinkedList
import LinkedList.Spec.DequeDoubly
import LinkedList.Spec.DoublyLinkedList
import LinkedList.Spec.DoublyLinkedListTwo
import LinkedList.Spec.FloydsCycleDetection
import LinkedList.Spec.FromSequence
import LinkedList.Spec.HasLoop
import LinkedList.Spec.IsPalindrome
import LinkedList.Spec.LinkedListInit
import LinkedList.Spec.MergeTwoLists
import LinkedList.Spec.MiddleElementOfLinkedList
import LinkedList.Spec.PrintReverse
import LinkedList.Spec.ReverseKGroup
import LinkedList.Spec.RotateToTheRight
import LinkedList.Spec.SinglyLinkedList
import LinkedList.Spec.SkipList
import LinkedList.Spec.SwapNodes
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_sll_insertHead_cons : spec_sll_insertHead_cons canonical := by
  unfold spec_sll_insertHead_cons
  intros
  rfl

#print axioms structural_spec_sll_insertHead_cons

theorem structural_spec_sll_insertTail_snoc : spec_sll_insertTail_snoc canonical := by
  unfold spec_sll_insertTail_snoc
  intros
  rfl

#print axioms structural_spec_sll_insertTail_snoc

theorem structural_spec_sll_insertNth_split : spec_sll_insertNth_split canonical := by
  unfold spec_sll_insertNth_split
  intros
  rfl

#print axioms structural_spec_sll_insertNth_split

theorem structural_spec_sll_isEmpty_iff_nil : spec_sll_isEmpty_iff_nil canonical := by
  unfold spec_sll_isEmpty_iff_nil
  intros
  rfl

#print axioms structural_spec_sll_isEmpty_iff_nil

theorem structural_spec_sll_reverse_eq_listReverse : spec_sll_reverse_eq_listReverse canonical := by
  unfold spec_sll_reverse_eq_listReverse
  intros
  rfl

#print axioms structural_spec_sll_reverse_eq_listReverse

theorem structural_spec_dll_insertAtHead_cons : spec_dll_insertAtHead_cons canonical := by
  unfold spec_dll_insertAtHead_cons
  intros
  rfl

#print axioms structural_spec_dll_insertAtHead_cons

theorem structural_spec_dll_insertAtTail_snoc : spec_dll_insertAtTail_snoc canonical := by
  unfold spec_dll_insertAtTail_snoc
  intros
  rfl

#print axioms structural_spec_dll_insertAtTail_snoc

theorem structural_spec_dll_insertAtNth_split : spec_dll_insertAtNth_split canonical := by
  unfold spec_dll_insertAtNth_split
  intros
  rfl

#print axioms structural_spec_dll_insertAtNth_split

theorem structural_spec_dll_isEmpty_iff_nil : spec_dll_isEmpty_iff_nil canonical := by
  unfold spec_dll_isEmpty_iff_nil
  intros
  rfl

#print axioms structural_spec_dll_isEmpty_iff_nil

theorem structural_spec_cll_insertHead_cons : spec_cll_insertHead_cons canonical := by
  unfold spec_cll_insertHead_cons
  intros
  rfl

#print axioms structural_spec_cll_insertHead_cons

theorem structural_spec_cll_insertTail_snoc : spec_cll_insertTail_snoc canonical := by
  unfold spec_cll_insertTail_snoc
  intros
  rfl

#print axioms structural_spec_cll_insertTail_snoc

theorem structural_spec_cll_insertNth_split : spec_cll_insertNth_split canonical := by
  unfold spec_cll_insertNth_split
  intros
  rfl

#print axioms structural_spec_cll_insertNth_split

theorem structural_spec_cll_isEmpty_iff_nil : spec_cll_isEmpty_iff_nil canonical := by
  unfold spec_cll_isEmpty_iff_nil
  intros
  rfl

#print axioms structural_spec_cll_isEmpty_iff_nil

theorem structural_spec_deque_first_head : spec_deque_first_head canonical := by
  unfold spec_deque_first_head
  intros
  rfl

#print axioms structural_spec_deque_first_head

theorem structural_spec_deque_last_getLast : spec_deque_last_getLast canonical := by
  unfold spec_deque_last_getLast
  intros
  rfl

#print axioms structural_spec_deque_last_getLast

theorem structural_spec_deque_addFirst_cons : spec_deque_addFirst_cons canonical := by
  unfold spec_deque_addFirst_cons
  intros
  rfl

#print axioms structural_spec_deque_addFirst_cons

theorem structural_spec_deque_addLast_snoc : spec_deque_addLast_snoc canonical := by
  unfold spec_deque_addLast_snoc
  intros
  rfl

#print axioms structural_spec_deque_addLast_snoc

theorem structural_spec_deque_isEmpty_iff_nil : spec_deque_isEmpty_iff_nil canonical := by
  unfold spec_deque_isEmpty_iff_nil
  intros
  rfl

#print axioms structural_spec_deque_isEmpty_iff_nil

theorem structural_spec_deque_addFirst_first_inverse : spec_deque_addFirst_first_inverse canonical := by
  unfold spec_deque_addFirst_first_inverse
  intros
  rfl

#print axioms structural_spec_deque_addFirst_first_inverse

theorem structural_spec_midll_push_cons : spec_midll_push_cons canonical := by
  unfold spec_midll_push_cons
  intros
  rfl

#print axioms structural_spec_midll_push_cons

theorem structural_spec_lli_add_split : spec_lli_add_split canonical := by
  unfold spec_lli_add_split
  intros
  rfl

#print axioms structural_spec_lli_add_split

theorem structural_spec_lli_isEmpty_iff_nil : spec_lli_isEmpty_iff_nil canonical := by
  unfold spec_lli_isEmpty_iff_nil
  intros
  rfl

#print axioms structural_spec_lli_isEmpty_iff_nil

theorem structural_spec_lli_length_eq_listLength : spec_lli_length_eq_listLength canonical := by
  unfold spec_lli_length_eq_listLength
  intros
  rfl

#print axioms structural_spec_lli_length_eq_listLength

theorem structural_spec_skipl_find_empty : spec_skipl_find_empty canonical := by
  unfold spec_skipl_find_empty
  intros
  rfl

#print axioms structural_spec_skipl_find_empty

theorem structural_spec_swap_push_cons : spec_swap_push_cons canonical := by
  unfold spec_swap_push_cons
  intros
  rfl

#print axioms structural_spec_swap_push_cons

theorem structural_spec_dll2_setTail_none_dropLast : spec_dll2_setTail_none_dropLast canonical := by
  unfold spec_dll2_setTail_none_dropLast
  intros
  rfl

#print axioms structural_spec_dll2_setTail_none_dropLast

theorem structural_spec_dll2_insert_cons : spec_dll2_insert_cons canonical := by
  unfold spec_dll2_insert_cons
  intros
  rfl

#print axioms structural_spec_dll2_insert_cons

theorem structural_spec_dll2_insertAtPosition_split : spec_dll2_insertAtPosition_split canonical := by
  unfold spec_dll2_insertAtPosition_split
  intros
  rfl

#print axioms structural_spec_dll2_insertAtPosition_split

theorem structural_spec_dll2_deleteValue_filters_all : spec_dll2_deleteValue_filters_all canonical := by
  unfold spec_dll2_deleteValue_filters_all
  intros
  rfl

#print axioms structural_spec_dll2_deleteValue_filters_all

theorem structural_spec_dll2_isEmpty_iff_nil : spec_dll2_isEmpty_iff_nil canonical := by
  unfold spec_dll2_isEmpty_iff_nil
  intros
  rfl

#print axioms structural_spec_dll2_isEmpty_iff_nil

theorem structural_spec_dll2_headData_eq_head : spec_dll2_headData_eq_head canonical := by
  unfold spec_dll2_headData_eq_head
  intros
  rfl

#print axioms structural_spec_dll2_headData_eq_head

theorem structural_spec_dll2_tailData_eq_getLast : spec_dll2_tailData_eq_getLast canonical := by
  unfold spec_dll2_tailData_eq_getLast
  intros
  rfl

#print axioms structural_spec_dll2_tailData_eq_getLast

theorem structural_spec_revk_append_snoc : spec_revk_append_snoc canonical := by
  unfold spec_revk_append_snoc
  intros
  rfl

#print axioms structural_spec_revk_append_snoc

theorem structural_spec_rotate_insertNode_snoc : spec_rotate_insertNode_snoc canonical := by
  unfold spec_rotate_insertNode_snoc
  intros
  rfl

#print axioms structural_spec_rotate_insertNode_snoc

theorem structural_spec_rotate_empty_id : spec_rotate_empty_id canonical := by
  unfold spec_rotate_empty_id
  intros
  rfl

#print axioms structural_spec_rotate_empty_id

theorem structural_spec_floyd_addNode_snoc : spec_floyd_addNode_snoc canonical := by
  unfold spec_floyd_addNode_snoc
  intros
  rfl

#print axioms structural_spec_floyd_addNode_snoc

theorem structural_spec_palindrome_isPalindrome_eq_reverse : spec_palindrome_isPalindrome_eq_reverse canonical := by
  unfold spec_palindrome_isPalindrome_eq_reverse
  intros
  rfl

#print axioms structural_spec_palindrome_isPalindrome_eq_reverse

theorem structural_spec_palindrome_isPalindromeDict_agrees : spec_palindrome_isPalindromeDict_agrees canonical := by
  unfold spec_palindrome_isPalindromeDict_agrees
  intros
  rfl

#print axioms structural_spec_palindrome_isPalindromeDict_agrees

theorem structural_spec_palindrome_agrees_with_print_reverse : spec_palindrome_agrees_with_print_reverse canonical := by
  unfold spec_palindrome_agrees_with_print_reverse
  intros
  rfl

#print axioms structural_spec_palindrome_agrees_with_print_reverse

theorem structural_spec_printrev_makeLinkedList_id : spec_printrev_makeLinkedList_id canonical := by
  unfold spec_printrev_makeLinkedList_id
  intros
  rfl

#print axioms structural_spec_printrev_makeLinkedList_id

theorem structural_spec_printrev_inReverse_eq_reverse : spec_printrev_inReverse_eq_reverse canonical := by
  unfold spec_printrev_inReverse_eq_reverse
  intros
  rfl

#print axioms structural_spec_printrev_inReverse_eq_reverse
