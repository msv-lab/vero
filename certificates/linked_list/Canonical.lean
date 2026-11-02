import Aesop
import Lean.Elab.Tactic.Omega
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
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_merge_fromList_empty : spec_merge_fromList_empty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_merge_fromList_empty, canonical]
  | solve | unfold spec_merge_fromList_empty; dsimp [canonical]; aesop
  | solve | unfold spec_merge_fromList_empty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_merge_fromList_empty
