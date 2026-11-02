import Lean.Elab.Tactic.Omega
import Huffman.Spec.BTree
import Huffman.Spec.Cover

set_option maxHeartbeats 5000

private theorem inb_transitive {A : Type} {a b c : BTree A} (hab : inb a b) (hbc : inb b c) : inb a c := by
  induction hbc with
  | inleaf => exact hab
  | innodeL l r _ ih => exact inb.innodeL _ l r ih
  | innodeR l r _ ih => exact inb.innodeR _ l r ih

private theorem inb_nodes_le {A : Type} {a b : BTree A} (h : inb a b) : number_of_nodes a ≤ number_of_nodes b := by
  induction h with
  | inleaf => omega
  | innodeL l r _ ih => simp only [number_of_nodes]; omega
  | innodeR l r _ ih => simp only [number_of_nodes]; omega

private theorem inb_eq_or_nodes_lt {A : Type} {a b : BTree A} (h : inb a b) : a = b ∨ number_of_nodes a < number_of_nodes b := by
  cases h with
  | inleaf => exact Or.inl rfl
  | innodeL l r hl =>
    have hh := inb_nodes_le hl
    right
    simp only [number_of_nodes]
    omega
  | innodeR l r hr =>
    have hh := inb_nodes_le hr
    right
    simp only [number_of_nodes]
    omega

theorem manual_spec_inb_trans :
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 t2 t3 : BTree A,
    inb t1 t2 → inb t2 t3 → inb t1 t3 := by
  intro A _inst _empty a b c hab hbc
  exact inb_transitive hab hbc
#print axioms manual_spec_inb_trans

theorem manual_spec_number_of_nodes_inb_le :
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 t2 : BTree A,
    inb t1 t2 → number_of_nodes t1 ≤ number_of_nodes t2 := by
  intro A _inst _empty a b hab
  exact inb_nodes_le hab
#print axioms manual_spec_number_of_nodes_inb_le

theorem manual_spec_inb_antisym :
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 t2 : BTree A,
    inb t1 t2 → inb t2 t1 → t1 = t2 := by
  intro A _inst _empty a b hab hba
  rcases inb_eq_or_nodes_lt hab with he | hlt
  · exact he
  · have hle := inb_nodes_le hba
    omega
#print axioms manual_spec_inb_antisym

theorem manual_spec_inb_ex :
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t : BTree A, ∃ x, inb (BTree.leaf x) t := by
  intro A _inst _empty t
  induction t with
  | leaf a => exact ⟨a, inb.inleaf _⟩
  | node l r ihl _ihr =>
    obtain ⟨a, ha⟩ := ihl
    exact ⟨a, inb.innodeL _ l r ha⟩
#print axioms manual_spec_inb_ex

theorem manual_spec_distinct_leaves_leaf :
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ a : A, distinct_leaves (BTree.leaf a) := by
  intro A _inst _empty a t0 t1 t2 h
  cases h
#print axioms manual_spec_distinct_leaves_leaf

theorem manual_spec_distinct_leaves_l :
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 t2 : BTree A,
    distinct_leaves (BTree.node t1 t2) → distinct_leaves t1 := by
  intro A _inst _empty l r hd a b c hnode hab hac
  exact hd a b c (inb.innodeL _ l r hnode) hab hac
#print axioms manual_spec_distinct_leaves_l

theorem manual_spec_distinct_leaves_r :
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t1 t2 : BTree A,
    distinct_leaves (BTree.node t1 t2) → distinct_leaves t2 := by
  intro A _inst _empty l r hd a b c hnode hab hac
  exact hd a b c (inb.innodeR _ l r hnode) hab hac
#print axioms manual_spec_distinct_leaves_r



theorem manual_spec_cover_not_nil :
  ∀ (A : Type), ∀ (l : List (BTree A)) (t : BTree A), cover l t → l ≠ [] := by
  intro A l t h
  cases h with
  | cover_one => simp
  | cover_node l1 rest a b t3 hp _h =>
    intro he
    have hl := hp.length_eq
    simp [he] at hl
#print axioms manual_spec_cover_not_nil

theorem manual_spec_cover_permutation :
  ∀ (A : Type), ∀ (t : BTree A) (l1 l2 : List (BTree A)),
    cover l1 t → List.Perm l1 l2 → cover l2 t := by
  intro A t l1 l2 h hp
  cases h with
  | cover_one =>
    have he : l2 = [t] := by simpa using hp.symm
    subst l2
    exact cover.cover_one t
  | cover_node l1 rest a b t3 hm hc =>
    exact cover.cover_node l2 rest a b t (hp.symm.trans hm) hc
#print axioms manual_spec_cover_permutation

theorem manual_spec_cover_one_inv :
  ∀ (A : Type), ∀ t1 t2 : BTree A, cover (t1 :: []) t2 → t1 = t2 := by
  intro A t1 t2 h
  cases h with
  | cover_one => rfl
  | cover_node l1 rest a b t3 hp _h =>
    have hl := hp.length_eq
    simp at hl
#print axioms manual_spec_cover_one_inv

private theorem cover_leaf_inverse {A : Type} {l : List (BTree A)} {t : BTree A} (h : cover l t) :
    ∀ a : A, t = BTree.leaf a → l = [BTree.leaf a] := by
  induction h with
  | cover_one t =>
    intro a he
    simp [he]
  | cover_node l1 rest t1 t2 t3 hp hc ih =>
    intro a he
    have hi := ih a he
    cases hi

theorem manual_spec_cover_inv_leaf :
  ∀ (A : Type), ∀ (a : A) (l : List (BTree A)),
    cover l (BTree.leaf a) → l = BTree.leaf a :: [] := by
  intro A a l h
  exact cover_leaf_inverse h a rfl
#print axioms manual_spec_cover_inv_leaf



private theorem all_leaves_of_inb {A : Type} {a : A} {t : BTree A} (h : inb (BTree.leaf a) t) :
    a ∈ Huffman.all_leaves A t := by
  induction h with
  | inleaf => simp [Huffman.all_leaves, Huffman.all_leaves.go]
  | innodeL l r _ ih =>
    have hm : a ∈ Huffman.all_leaves A l ∨ a ∈ Huffman.all_leaves A r := Or.inl ih
    simpa [Huffman.all_leaves, Huffman.all_leaves.go] using hm
  | innodeR l r _ ih =>
    have hm : a ∈ Huffman.all_leaves A l ∨ a ∈ Huffman.all_leaves A r := Or.inr ih
    simpa [Huffman.all_leaves, Huffman.all_leaves.go] using hm

private theorem inb_of_all_leaves {A : Type} (t : BTree A) (a : A) (h : a ∈ Huffman.all_leaves A t) :
    inb (BTree.leaf a) t := by
  induction t with
  | leaf x =>
    simp [Huffman.all_leaves, Huffman.all_leaves.go] at h
    subst a
    exact inb.inleaf _
  | node l r ihl ihr =>
    have hm : a ∈ Huffman.all_leaves A l ∨ a ∈ Huffman.all_leaves A r := by
      simpa [Huffman.all_leaves, Huffman.all_leaves.go] using h
    rcases hm with hl | hr
    · exact inb.innodeL _ l r (ihl hl)
    · exact inb.innodeR _ l r (ihr hr)

theorem manual_spec_all_leaves_in :
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t a,
    inb (BTree.leaf a) t → a ∈ Huffman.all_leaves A t := by
  intro A _inst _empty t a h
  exact all_leaves_of_inb h
#print axioms manual_spec_all_leaves_in

theorem manual_spec_all_leaves_inb :
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t a,
    a ∈ Huffman.all_leaves A t → inb (BTree.leaf a) t := by
  intro A _inst _empty t a h
  exact inb_of_all_leaves t a h
#print axioms manual_spec_all_leaves_inb


private theorem all_leaves_nodup {A : Type} (t : BTree A) (hd : distinct_leaves t) :
    (Huffman.all_leaves A t).Nodup := by
  induction t with
  | leaf a => simp [Huffman.all_leaves, Huffman.all_leaves.go]
  | node l r ihl ihr =>
    have dl : distinct_leaves l := by
      intro a b c hn hab hac
      exact hd a b c (inb.innodeL _ l r hn) hab hac
    have dr : distinct_leaves r := by
      intro a b c hn hab hac
      exact hd a b c (inb.innodeR _ l r hn) hab hac
    change (Huffman.all_leaves A l ++ Huffman.all_leaves A r).Nodup
    apply List.Nodup.append (ihl dl) (ihr dr)
    intro a ha hb
    exact hd (BTree.leaf a) l r (inb.inleaf _) (inb_of_all_leaves l a ha) (inb_of_all_leaves r a hb)

theorem manual_spec_all_leaves_NoDup :
  ∀ (A : Type) [DecidableEq A] (empty : A), ∀ t,
    distinct_leaves t → List.Nodup (Huffman.all_leaves A t) := by
  intro A _inst _empty t h
  exact all_leaves_nodup t h
#print axioms manual_spec_all_leaves_NoDup
