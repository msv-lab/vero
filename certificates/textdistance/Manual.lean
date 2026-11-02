import Textdistance.Spec.Edit

set_option maxHeartbeats 3000

theorem manual_spec_lev_empty_left : spec_lev_empty_left canonical := by
  intro b
  simp [canonical, Textdistance.levenshtein, Textdistance.levenshteinGo]
#print axioms manual_spec_lev_empty_left

theorem manual_spec_lev_empty_right : spec_lev_empty_right canonical := by
  intro a
  cases a <;> simp [canonical, Textdistance.levenshtein, Textdistance.levenshteinGo]
#print axioms manual_spec_lev_empty_right

theorem manual_spec_lev_self_zero : spec_lev_self_zero canonical := by
  intro a
  induction a with
  | nil => simp [canonical, Textdistance.levenshtein, Textdistance.levenshteinGo]
  | cons x xs ih => simpa [canonical, Textdistance.levenshtein, Textdistance.levenshteinGo] using ih
#print axioms manual_spec_lev_self_zero

theorem manual_spec_lev_cons_eq_head : spec_lev_cons_eq_head canonical := by
  intro x xs ys
  simp [canonical, Textdistance.levenshtein, Textdistance.levenshteinGo]
#print axioms manual_spec_lev_cons_eq_head

theorem manual_spec_lev_cons_cons : spec_lev_cons_cons canonical := by
  intro x xs y ys
  simp [canonical, Textdistance.levenshtein, Textdistance.levenshteinGo]
#print axioms manual_spec_lev_cons_cons

theorem manual_spec_lcs_empty : spec_lcs_empty canonical := by
  intro b
  simp [canonical, Textdistance.lcs, Textdistance.lcsGo]
#print axioms manual_spec_lcs_empty

theorem manual_spec_lcs_empty_right : spec_lcs_empty_right canonical := by
  intro a
  cases a <;> simp [canonical, Textdistance.lcs, Textdistance.lcsGo]
#print axioms manual_spec_lcs_empty_right

theorem manual_spec_lcs_self : spec_lcs_self canonical := by
  intro a
  induction a with
  | nil => simp [canonical, Textdistance.lcs, Textdistance.lcsGo]
  | cons x xs ih => simpa [canonical, Textdistance.lcs, Textdistance.lcsGo, Nat.add_comm] using congrArg Nat.succ ih
#print axioms manual_spec_lcs_self

theorem manual_spec_lcs_cons_eq_head : spec_lcs_cons_eq_head canonical := by
  intro x xs ys
  simp [canonical, Textdistance.lcs, Textdistance.lcsGo]
#print axioms manual_spec_lcs_cons_eq_head

theorem manual_spec_lcs_cons_cons : spec_lcs_cons_cons canonical := by
  intro x xs y ys
  simp [canonical, Textdistance.lcs, Textdistance.lcsGo]
#print axioms manual_spec_lcs_cons_cons
