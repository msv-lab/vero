import Flocq.Calc.Impl.Sqrt
import Mathlib.Tactic.NormNum

namespace FlocqCertificates

theorem zdiv2_floor_bounds (n : Int) :
    2 * Flocq.zdiv2 n ≤ n ∧ n < 2 * (Flocq.zdiv2 n + 1) := by
  unfold Flocq.zdiv2
  omega

theorem zdiv2_negative_odd (k : Nat) :
    Flocq.zdiv2 (-((2 * k + 1 : Nat) : Int)) = -((k : Int) + 1) := by
  unfold Flocq.zdiv2
  omega

theorem zdiv2_negative_one : Flocq.zdiv2 (-1) = -1 := by rfl

theorem spec_fsqrtCore_mantissa : ∀ (beta : Radix) (m1 e1 e : Int),
    0 < m1 → 2 * e ≤ e1 →
    let m1' := m1 * beta.val ^ (e1 - 2 * e).toNat
    (Flocq.fsqrtCore beta m1 e1 e).1 * (Flocq.fsqrtCore beta m1 e1 e).1 ≤ m1' ∧
    m1' < ((Flocq.fsqrtCore beta m1 e1 e).1 + 1) *
      ((Flocq.fsqrtCore beta m1 e1 e).1 + 1) := by
  intro beta m e1 e hm he
  have hb : 0 < beta.val := by have := beta.h; omega
  have ha : 0 ≤ m * beta.val ^ (e1 - 2 * e).toNat :=
    le_of_lt (mul_pos hm (pow_pos hb _))
  have hc : (((m * beta.val ^ (e1 - 2 * e).toNat).toNat : Nat) : Int) =
      m * beta.val ^ (e1 - 2 * e).toNat := Int.toNat_of_nonneg ha
  obtain ⟨hl, hu⟩ := Flocq.isqrt_bounds (m * beta.val ^ (e1 - 2 * e).toNat).toNat
  dsimp only [Flocq.fsqrtCore]
  constructor
  · have h := Int.ofNat_le.mpr hl
    simpa only [Int.natCast_mul, hc] using h
  · have h := Int.ofNat_lt.mpr hu
    simpa only [Int.natCast_mul, Int.natCast_add, Int.natCast_one, hc] using h

theorem spec_fsqrtCore_exact : ∀ (beta : Radix) (m1 e1 e : Int),
    0 < m1 → 2 * e ≤ e1 →
    let m1' := m1 * beta.val ^ (e1 - 2 * e).toNat
    let q := (Flocq.fsqrtCore beta m1 e1 e).1
    m1' = q * q → (Flocq.fsqrtCore beta m1 e1 e).2 = Location.Exact := by
  intro beta m e1 e hm he
  dsimp only
  intro h
  let q := (Flocq.fsqrtCore beta m e1 e).1
  let r := m * beta.val ^ (e1 - 2 * e).toNat - q * q
  have hr : r = 0 := sub_eq_zero.mpr h
  change (if r = 0 then Location.Exact else Location.Inexact (if r ≤ q then Ordering.lt else Ordering.gt)) = _
  simp only [hr, ↓reduceIte]

theorem spec_fsqrtCore_inexact_lo : ∀ (beta : Radix) (m1 e1 e : Int),
    0 < m1 → 2 * e ≤ e1 →
    let m1' := m1 * beta.val ^ (e1 - 2 * e).toNat
    let q := (Flocq.fsqrtCore beta m1 e1 e).1
    let r := m1' - q * q
    r ≠ 0 → r ≤ q → (Flocq.fsqrtCore beta m1 e1 e).2 = Location.Inexact Ordering.lt := by
  intro beta m e1 e hm he
  dsimp only
  intro hn hle
  let q := (Flocq.fsqrtCore beta m e1 e).1
  let r := m * beta.val ^ (e1 - 2 * e).toNat - q * q
  change (if r = 0 then Location.Exact else Location.Inexact (if r ≤ q then Ordering.lt else Ordering.gt)) = _
  simp only [show r ≠ 0 from hn, show r ≤ q from hle, ↓reduceIte]

theorem spec_fsqrtCore_inexact_hi : ∀ (beta : Radix) (m1 e1 e : Int),
    0 < m1 → 2 * e ≤ e1 →
    let m1' := m1 * beta.val ^ (e1 - 2 * e).toNat
    let q := (Flocq.fsqrtCore beta m1 e1 e).1
    let r := m1' - q * q
    r ≠ 0 → r > q → (Flocq.fsqrtCore beta m1 e1 e).2 = Location.Inexact Ordering.gt := by
  intro beta m e1 e hm he
  dsimp only
  intro hn hgt
  let q := (Flocq.fsqrtCore beta m e1 e).1
  let r := m * beta.val ^ (e1 - 2 * e).toNat - q * q
  change (if r = 0 then Location.Exact else Location.Inexact (if r ≤ q then Ordering.lt else Ordering.gt)) = _
  simp only [show r ≠ 0 from hn, show ¬ r ≤ q from not_le.mpr hgt, ↓reduceIte]

end FlocqCertificates

#print axioms FlocqCertificates.zdiv2_floor_bounds
#print axioms FlocqCertificates.zdiv2_negative_odd
#print axioms FlocqCertificates.spec_fsqrtCore_mantissa
#print axioms FlocqCertificates.spec_fsqrtCore_exact
#print axioms FlocqCertificates.spec_fsqrtCore_inexact_lo
#print axioms FlocqCertificates.spec_fsqrtCore_inexact_hi
