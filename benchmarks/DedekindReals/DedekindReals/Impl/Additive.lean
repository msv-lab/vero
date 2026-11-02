import DedekindReals.Impl.Cut

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DedekindReals.Impl.Additive

Addition, additive inverse, and subtraction for Dedekind cuts.

DO NOT MODIFY types or signatures -- these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace DedekindReals

-- !benchmark @start global_aux


-- !benchmark @end global_aux

namespace DedekindClosureSupport
open DedekindReals

theorem lower_upper (x : R) {a b : Rat} (ha : x.lower a) (hb : x.upper b) : a < b := by
  by_contra h
  have hba : b ≤ a := le_of_not_gt h
  rcases lt_or_eq_of_le hba with hba | hba
  · exact x.disjoint a ⟨ha, x.upper_upper b a hba hb⟩
  · subst a; exact x.disjoint b ⟨ha, hb⟩

theorem lower_le (x : R) {a b : Rat} (h : a ≤ b) (hb : x.lower b) : x.lower a := by
  rcases lt_or_eq_of_le h with h | h
  · exact x.lower_lower a b h hb
  · subst a; exact hb

theorem upper_le (x : R) {a b : Rat} (h : a ≤ b) (ha : x.upper a) : x.upper b := by
  rcases lt_or_eq_of_le h with h | h
  · exact x.upper_upper a b h ha
  · subst a; exact ha

theorem straddle (x : R) (eps : Rat) (heps : 0 < eps) :
    ∃ a b : Rat, x.lower a ∧ x.upper b ∧ b - a < eps := by
  classical
  obtain ⟨l, hl⟩ := x.lower_bound
  obtain ⟨u, hu⟩ := x.upper_bound
  let d := eps / 3
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt ((u - l) / d)
  have hn' : u < l + (n : Rat) * d := by
    have := (div_lt_iff₀ hd).mp hn
    linarith
  have hex : ∃ n : Nat, x.upper (l + (n : Rat) * d) :=
    ⟨n, x.upper_upper u _ hn' hu⟩
  let k := Nat.find hex
  have hfind : Nat.find hex = k := rfl
  have hk : x.upper (l + (k : Rat) * d) := Nat.find_spec hex
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    simp only [hk0, Nat.cast_zero, zero_mul, add_zero] at hk
    exact x.disjoint l ⟨hl, hk⟩
  rcases k with _ | k
  · omega
  rcases k with _ | k
  · refine ⟨l, l + (1 : Rat) * d, hl, hk, ?_⟩
    dsimp [d]; linarith
  · have hnot : ¬x.upper (l + ((k + 1 : Nat) : Rat) * d) :=
      Nat.find_min hex (by omega)
    have hlt : l + (k : Rat) * d < l + ((k + 1 : Nat) : Rat) * d := by
      push_cast; linarith
    have hlo := (x.located _ _ hlt).resolve_right hnot
    refine ⟨l + (k : Rat) * d, l + ((k + 2 : Nat) : Rat) * d, hlo, hk, ?_⟩
    push_cast; dsimp [d]; linarith

end DedekindClosureSupport

-- API signatures

abbrev RplusSig := R → R → R
abbrev RoppSig := R → R
abbrev RminusSig := R → R → R

end DedekindReals

-- Reference implementations

-- !benchmark @start code_aux def=Rplus
-- !benchmark @end code_aux def=Rplus
namespace DedekindReals
open DedekindClosureSupport

theorem Rplus_lower_bound :
  ∀ x y : R, ∃ q : Rat, ∃ r s : Rat, q < r + s ∧ x.lower r ∧ y.lower s := by
  intro x y
  obtain ⟨r, hr⟩ := x.lower_bound
  obtain ⟨s, hs⟩ := y.lower_bound
  exact ⟨r + s - 1, r, s, by linarith, hr, hs⟩

theorem Rplus_upper_bound :
  ∀ x y : R, ∃ q : Rat, ∃ r s : Rat, r + s < q ∧ x.upper r ∧ y.upper s := by
  intro x y
  obtain ⟨r, hr⟩ := x.upper_bound
  obtain ⟨s, hs⟩ := y.upper_bound
  exact ⟨r + s + 1, r, s, by linarith, hr, hs⟩

theorem Rplus_lower_open :
  ∀ (x y : R) (q : Rat),
    (∃ r s : Rat, q < r + s ∧ x.lower r ∧ y.lower s) →
      ∃ r : Rat, q < r ∧ ∃ u v : Rat, r < u + v ∧ x.lower u ∧ y.lower v := by
  intro x y q h
  obtain ⟨r, s, h, hr, hs⟩ := h
  exact ⟨(q + (r + s)) / 2, by linarith, r, s, by linarith, hr, hs⟩

theorem Rplus_upper_open :
  ∀ (x y : R) (q : Rat),
    (∃ r s : Rat, r + s < q ∧ x.upper r ∧ y.upper s) →
      ∃ r : Rat, r < q ∧ ∃ u v : Rat, u + v < r ∧ x.upper u ∧ y.upper v := by
  intro x y q h
  obtain ⟨r, s, h, hr, hs⟩ := h
  exact ⟨(q + (r + s)) / 2, by linarith, r, s, by linarith, hr, hs⟩

theorem Rplus_disjoint :
  ∀ (x y : R) (q : Rat),
    ¬ ((∃ r s : Rat, q < r + s ∧ x.lower r ∧ y.lower s) ∧
      (∃ r s : Rat, r + s < q ∧ x.upper r ∧ y.upper s)) := by
  intro x y q
  rintro ⟨⟨a, b, hab, ha, hb⟩, ⟨c, d, hcd, hc, hd⟩⟩
  have := lower_upper x ha hc
  have := lower_upper y hb hd
  linarith

theorem Rplus_located :
  ∀ (x y : R) (q r : Rat), q < r →
    (∃ u v : Rat, q < u + v ∧ x.lower u ∧ y.lower v) ∨
      (∃ u v : Rat, u + v < r ∧ x.upper u ∧ y.upper v) := by
  intro x y q r hqr
  obtain ⟨a, b, ha, hb, hab⟩ := straddle x ((r - q) / 3) (by linarith)
  obtain ⟨c, d, hc, hd, hcd⟩ := straddle y ((r - q) / 3) (by linarith)
  by_cases h : q < a + c
  · exact Or.inl ⟨a, c, h, ha, hc⟩
  · exact Or.inr ⟨b, d, by linarith, hb, hd⟩

end DedekindReals

def DedekindReals.Rplus : DedekindReals.RplusSig :=
-- !benchmark @start code def=Rplus
  fun x y =>
    { lower := fun q => ∃ r s : Rat, q < r + s ∧ x.lower r ∧ y.lower s
      upper := fun q => ∃ r s : Rat, r + s < q ∧ x.upper r ∧ y.upper s
      lower_proper := by
        intro q r hqr
        cases hqr
        rfl
      upper_proper := by
        intro q r hqr
        cases hqr
        rfl
      lower_bound := DedekindReals.Rplus_lower_bound x y
      upper_bound := DedekindReals.Rplus_upper_bound x y
      lower_lower := by
        intro q r hqr h
        rcases h with ⟨u, v, huv, hu, hv⟩
        exact ⟨u, v, by grind, hu, hv⟩
      lower_open := DedekindReals.Rplus_lower_open x y
      upper_upper := by
        intro q r hqr h
        rcases h with ⟨u, v, huv, hu, hv⟩
        exact ⟨u, v, by grind, hu, hv⟩
      upper_open := DedekindReals.Rplus_upper_open x y
      disjoint := DedekindReals.Rplus_disjoint x y
      located := DedekindReals.Rplus_located x y }
-- !benchmark @end code def=Rplus

-- !benchmark @start code_aux def=Ropp
-- !benchmark @end code_aux def=Ropp

def DedekindReals.Ropp : DedekindReals.RoppSig :=
-- !benchmark @start code def=Ropp
  fun x =>
    { lower := fun q => x.upper (-q)
      upper := fun q => x.lower (-q)
      lower_proper := by
        intro q r hqr
        cases hqr
        rfl
      upper_proper := by
        intro q r hqr
        cases hqr
        rfl
      lower_bound := by
        rcases x.upper_bound with ⟨r, hr⟩
        exact ⟨-r, by simpa using hr⟩
      upper_bound := by
        rcases x.lower_bound with ⟨q, hq⟩
        exact ⟨-q, by simpa using hq⟩
      lower_lower := by
        intro q r hqr hr
        exact x.upper_upper (-r) (-q) (by grind) hr
      lower_open := by
        intro q hq
        rcases x.upper_open (-q) hq with ⟨s, hslt, hs⟩
        exact ⟨-s, by grind, by simpa using hs⟩
      upper_upper := by
        intro q r hqr hq
        exact x.lower_lower (-r) (-q) (by grind) hq
      upper_open := by
        intro r hr
        rcases x.lower_open (-r) hr with ⟨q, hqlt, hq⟩
        exact ⟨-q, by grind, by simpa using hq⟩
      disjoint := by
        intro q h
        exact x.disjoint (-q) ⟨h.2, h.1⟩
      located := by
        intro q r hqr
        cases x.located (-r) (-q) (by grind) with
        | inl h => exact Or.inr (by simpa using h)
        | inr h => exact Or.inl (by simpa using h) }
-- !benchmark @end code def=Ropp

-- !benchmark @start code_aux def=Rminus
-- !benchmark @end code_aux def=Rminus

def DedekindReals.Rminus : DedekindReals.RminusSig :=
-- !benchmark @start code def=Rminus
  fun x y => DedekindReals.Rplus x (DedekindReals.Ropp y)
-- !benchmark @end code def=Rminus

namespace DedekindReals

-- Pure spec helpers.

def Rplus_comp : Prop :=
  ∀ x y u v : R, Req x y → Req u v → Req (Rplus x u) (Rplus y v)

def Ropp_comp : Prop := ∀ x y : R, Req x y → Req (Ropp x) (Ropp y)

def sum_interval_lower : Prop :=
  ∀ (x y : R) (a b : Rat), x.lower a → y.lower b → (Rplus x y).lower (a + b)

def sum_interval_upper : Prop :=
  ∀ (x y : R) (a b : Rat), x.upper a → y.upper b → (Rplus x y).upper (a + b)

end DedekindReals
