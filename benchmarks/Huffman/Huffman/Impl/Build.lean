import Mathlib.Data.List.Sort
import Huffman.Impl.WeightTree
import Huffman.Impl.Weight
import Huffman.Impl.BTree
import Huffman.Impl.SameSumLeaves
import Huffman.Impl.ISort
import Huffman.Impl.Cover
import Huffman.Impl.CoverMin
import Huffman.Impl.AuxLib
import Huffman.Impl.Ordered
import Huffman.Impl.OneStep

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Huffman.Impl.Build

Build-process vocabulary and opaque construction APIs translated from
Coq's `Build.v`. The inductive `build` predicate is frozen vocabulary;
the API declarations below expose the selected construction functions.

DO NOT MODIFY types or signatures — these are the fixed vocabulary.
Implement only the function bodies.
-/

inductive build {A : Type} (f : A → Nat) : List (BTree A) → BTree A → Prop where
  | build_one : ∀ t, build f [t] t
  | build_step : ∀ l1 l2 t, one_step f l1 l2 → build f l2 t → build f l1 t

namespace Huffman

abbrev BuildFunSig :=
  (A : Type) → (f : A → Nat) → (l : List (BTree A)) → l ≠ [] → {t : BTree A // cover_min A f l t}

abbrev BuildfSig :=
  (A : Type) → (f : A → Nat) → (l : List (BTree A)) → l ≠ [] → {t : BTree A // build f l t}

abbrev ObuildfSig :=
  (A : Type) → (f : A → Nat) → (l : List (BTree A)) → l ≠ [] →
    ordered (fun x y => Huffman.sum_leaves A f x ≤ Huffman.sum_leaves A f y) l →
    {t : BTree A // build f l t}

end Huffman

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=build_fun
-- !benchmark @end code_aux def=build_fun

axiom Huffman.build_fun_witness : Huffman.BuildFunSig

noncomputable def Huffman.build_fun : Huffman.BuildFunSig :=
-- !benchmark @start code def=build_fun
  Huffman.build_fun_witness
-- !benchmark @end code def=build_fun

-- !benchmark @start code_aux def=buildf
private theorem huffman_sorted_ordered {A : Type} {r : A → A → Prop} {l : List A}
    (h : List.Pairwise r l) : ordered r l := by
  induction l with
  | nil => exact .ordered_nil
  | cons a as ih =>
    cases as with
    | nil => exact .ordered_one a
    | cons b bs =>
      exact .ordered_cons a b bs ((List.pairwise_cons.mp h).1 b (by simp)) (ih h.tail)

private theorem huffman_sort_ordered {A : Type} (f : A → Nat) (l : List (BTree A)) :
    ordered (sum_order f) (l.mergeSort (le_sum f)) := by
  apply huffman_sorted_ordered
  have hs := List.pairwise_mergeSort
    (le := le_sum f)
    (fun a b c h1 h2 => by simp [le_sum] at h1 h2 ⊢; exact Nat.le_trans h1 h2)
    (fun a b => by simp [le_sum, Bool.or_eq_true]; omega) l
  simpa only [le_sum, decide_eq_true_eq, sum_order] using hs

def Huffman.buildf_witness (A : Type) (f : A → Nat) (l : List (BTree A))
    (hn : l ≠ []) : {t : BTree A // build f l t} := by
  let s := l.mergeSort (le_sum f)
  have hp : s.Perm l := List.mergeSort_perm l _
  have ho : ordered (sum_order f) s := huffman_sort_ordered f l
  cases hs : s with
  | nil =>
    have he : l = [] := by simpa [hs] using hp.symm
    exact False.elim (hn he)
  | cons a as =>
    cases as with
    | nil =>
      have he : l = [a] := by simpa [hs] using hp.symm
      exact ⟨a, he ▸ build.build_one a⟩
    | cons b rest =>
      have hlen := hp.length_eq
      have hl : (BTree.node a b :: rest).length < l.length := by simp [hs] at hlen; simp; omega
      let result := Huffman.buildf_witness A f (BTree.node a b :: rest) (by simp)
      refine ⟨result.val, build.build_step l (BTree.node a b :: rest) result.val ?_ result.property⟩
      exact ⟨a, b, rest, hs ▸ ho, by simpa [hs] using hp.symm, List.Perm.refl _⟩
termination_by l.length
-- !benchmark @end code_aux def=buildf

noncomputable def Huffman.buildf : Huffman.BuildfSig :=
-- !benchmark @start code def=buildf
  Huffman.buildf_witness
-- !benchmark @end code def=buildf

-- !benchmark @start code_aux def=obuildf
noncomputable def Huffman.obuildf_witness : Huffman.ObuildfSig :=
  fun A f l hn _ => Huffman.buildf_witness A f l hn
-- !benchmark @end code_aux def=obuildf

noncomputable def Huffman.obuildf : Huffman.ObuildfSig :=
-- !benchmark @start code def=obuildf
  Huffman.obuildf_witness
-- !benchmark @end code def=obuildf
