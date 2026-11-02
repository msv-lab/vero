import Huffman.Impl.CoverMin
namespace CanonicalAxiomAudit
inductive OldCover {A : Type} : List (BTree A) → BTree A → Prop where
  | leaf : ∀ a, OldCover [.leaf a] (.leaf a)
  | node : ∀ l1 l2 t1 t2, OldCover l1 t1 → OldCover l2 t2 → OldCover (l1 ++ l2) (.node t1 t2)
private theorem old_cover_leaves {A : Type} {l : List (BTree A)} {t : BTree A} (h : OldCover l t) :
    ∀ x ∈ l, ∃ a, x = BTree.leaf a := by
  induction h with
  | leaf a => simp
  | node l1 l2 t1 t2 _ _ ih1 ih2 =>
    intro x hx
    simp only [List.mem_append] at hx
    cases hx with
    | inl h => exact ih1 x h
    | inr h => exact ih2 x h

theorem old_build_fun_assumption_false
    (bad : ∀ (A : Type) (l : List (BTree A)), l ≠ [] → ∃ t, OldCover l t) : False := by
  obtain ⟨t, ht⟩ := bad Unit [.node (.leaf ()) (.leaf ())] (by simp)
  obtain ⟨a, ha⟩ := old_cover_leaves ht (.node (.leaf ()) (.leaf ())) (by simp)
  cases ha
#print axioms old_build_fun_assumption_false
end CanonicalAxiomAudit
