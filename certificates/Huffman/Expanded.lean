import Aesop
import Lean.Elab.Tactic.Omega
import Huffman.Spec.BTree
import Huffman.Spec.Build
import Huffman.Spec.Code
import Huffman.Spec.Cover
import Huffman.Spec.Frequency
import Huffman.Spec.HeightPred
import Huffman.Spec.Huffman
import Huffman.Spec.ISort
import Huffman.Spec.OneStep
import Huffman.Spec.OrderedCover
import Huffman.Spec.PBTree
import Huffman.Spec.PBTree2BTree
import Huffman.Spec.Prod2List
import Huffman.Spec.Restrict
import Huffman.Spec.Weight
import Huffman.Spec.WeightTree
set_option maxHeartbeats 5000
set_option maxRecDepth 512
theorem expanded_spec_frequency_list_restric_code_map :
  ∀ (A : Type) [DecidableEq A] (empty : A) (m : List A), ∀ c : Code A,
    List.map (fun p : A × Nat => p.1) (Huffman.frequency_list A m) =
      List.map (fun p : A × List Bool => p.1) (Huffman.restrict_code A m c) := by
  first
  | solve | intros; rfl
  | solve | simp_all [Huffman.frequency_list, Huffman.restrict_code]
  | solve | aesop
  | solve | intros; omega

#print axioms expanded_spec_frequency_list_restric_code_map
