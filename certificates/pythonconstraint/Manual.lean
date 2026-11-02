import Aesop
import Pythonconstraint.Spec.Csp

set_option maxHeartbeats 2000
open Pythonconstraint

private theorem lookup_reference (a : Assignment) (v : Nat) : lookup a v = refLookup a v := by
  induction a with
  | nil => rfl
  | cons p rest ih => cases p; simp [lookup, refLookup, ih]

private theorem values_reference (a : Assignment) (vs : List Nat) : values a vs = refValues a vs := by
  simp [values, refValues, lookup_reference]

private theorem distinct_reference (xs : List Nat) : allDistinct xs = refAllDistinct xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [allDistinct, refAllDistinct, ih]

private theorem holds_reference (c : Constraint) (a : Assignment) : holds c a = holdsRef c a := by
  cases c <;> simp [holds, holdsRef, values_reference, distinct_reference, sumList, refSumList, allInSet, refAllInSet]

private theorem enumerate_reference (ds : List (List Nat)) (i : Nat) : enumerate ds i = refEnumerate ds i := by
  induction ds generalizing i with
  | nil => rfl
  | cons d ds ih => simp [enumerate, refEnumerate, ih]

private theorem solutions_reference (ds : List (List Nat)) (cs : List Constraint) : getSolutions ds cs = modelList ds cs := by
  cases ds <;> simp [getSolutions, modelList, enumerate_reference, holds_reference]

private theorem solutions_membership (ds : List (List Nat)) (cs : List Constraint) (a : Assignment) :
    a ∈ getSolutions ds cs ↔ modelMember ds cs a := by
  cases ds <;> simp [getSolutions, modelMember, respectsDomains, satisfiesRef, enumerate_reference, holds_reference, List.mem_filter, List.all_eq_true]

theorem manual_spec_alldiff_iff : spec_alldiff_iff canonical := by
  intro vs a
  exact holds_reference (.allDifferent vs) a
#print axioms manual_spec_alldiff_iff

theorem manual_spec_exactsum_iff : spec_exactsum_iff canonical := by
  intro vs k a
  exact holds_reference (.exactSum vs k) a
#print axioms manual_spec_exactsum_iff

theorem manual_spec_holds_ref : spec_holds_ref canonical := by
  intro c a
  exact holds_reference c a
#print axioms manual_spec_holds_ref

theorem manual_spec_solutions_eq_modelset : spec_solutions_eq_modelset canonical := by
  intro ds cs a
  exact solutions_membership ds cs a
#print axioms manual_spec_solutions_eq_modelset

theorem manual_spec_solutions_sound : spec_solutions_sound canonical := by
  intro ds cs a h
  exact (solutions_membership ds cs a).mp h
#print axioms manual_spec_solutions_sound

theorem manual_spec_solutions_complete : spec_solutions_complete canonical := by
  intro ds cs a h
  exact (solutions_membership ds cs a).mpr h
#print axioms manual_spec_solutions_complete

theorem manual_spec_solutions_perm_model : spec_solutions_perm_model canonical := by
  intro ds cs
  change (getSolutions ds cs).Perm (modelList ds cs)
  rw [solutions_reference]
#print axioms manual_spec_solutions_perm_model

theorem manual_spec_count_eq_length : spec_count_eq_length canonical := by
  intro ds cs
  rfl
#print axioms manual_spec_count_eq_length

theorem manual_spec_no_variables_empty : spec_no_variables_empty canonical := by
  intro cs
  rfl
#print axioms manual_spec_no_variables_empty

theorem manual_spec_getSolution_iff : spec_getSolution_iff canonical := by
  intro ds cs
  change (getSolutions ds cs).head? ≠ none ↔ getSolutions ds cs ≠ []
  cases getSolutions ds cs <;> simp
#print axioms manual_spec_getSolution_iff

theorem manual_spec_getSolution_mem : spec_getSolution_mem canonical := by
  intro ds cs a h
  change (getSolutions ds cs).head? = some a at h
  change a ∈ getSolutions ds cs
  cases he : getSolutions ds cs with
  | nil => simp [he] at h
  | cons x xs =>
    simp [he] at h ⊢
    exact Or.inl h.symm
#print axioms manual_spec_getSolution_mem

theorem manual_spec_cons_constraint_filter : spec_cons_constraint_filter canonical := by
  intro ds c cs
  change getSolutions ds (c :: cs) = (getSolutions ds cs).filter (fun a => holdsRef c a)
  cases ds <;> simp [getSolutions, List.filter_filter, holds_reference]
#print axioms manual_spec_cons_constraint_filter


theorem manual_spec_count_zero_iff_no_model : spec_count_zero_iff_no_model canonical := by
  intro ds cs
  change (getSolutions ds cs).length = 0 ↔ ∀ a, ¬ modelMember ds cs a
  constructor
  · intro h a hm
    have he : getSolutions ds cs = [] := by
      cases hx : getSolutions ds cs with
      | nil => rfl
      | cons x xs => simp [hx] at h
    have hm' := (solutions_membership ds cs a).mpr hm
    simpa [he] using hm'
  · intro h
    cases he : getSolutions ds cs with
    | nil => rfl
    | cons x xs =>
      have hm : x ∈ getSolutions ds cs := by simp [he]
      exact False.elim (h x ((solutions_membership ds cs x).mp hm))
#print axioms manual_spec_count_zero_iff_no_model

private theorem enumerate_length (ds : List (List Nat)) (i : Nat) :
    (enumerate ds i).length = refDomainProduct ds := by
  induction ds generalizing i with
  | nil => rfl
  | cons d ds ih =>
    simp only [enumerate, refDomainProduct, List.length_flatMap, List.length_map, ih]
    induction d with
    | nil => simp
    | cons x xs hx => simp [hx, Nat.succ_mul, Nat.add_comm]

theorem manual_spec_count_no_constraints_product : spec_count_no_constraints_product canonical := by
  intro ds h
  change (getSolutions ds []).length = refDomainProduct ds
  cases ds with
  | nil => exact False.elim (h rfl)
  | cons d ds =>
    have hf (xs : List Assignment) : xs.filter (fun _ => true) = xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => simp [List.filter_cons, ih]
    change ((enumerate (d :: ds) 0).filter (fun _ => true)).length = refDomainProduct (d :: ds)
    rw [hf]
    exact enumerate_length (d :: ds) 0
#print axioms manual_spec_count_no_constraints_product
