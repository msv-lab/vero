import Flocq.Core.Impl.Digits
import Mathlib.Tactic

namespace FlocqCertificates

private theorem digitsAux_ge (a b k p : Int) (fuel : Nat) :
    k ≤ zdigitsAuxCore a b k p fuel := by
  induction fuel generalizing k p with
  | zero => exact le_refl _
  | succ fuel ih =>
    simp only [zdigitsAuxCore]
    split
    · exact le_refl _
    · exact le_trans (by omega) (ih (k + 1) (b * p))

theorem spec_zdigits_nonneg : ∀ (r : Radix) (n : Int),
    0 ≤ Flocq.zdigits r n := by
  intro r n
  unfold Flocq.zdigits
  split
  · omega
  · exact le_trans (by omega) (digitsAux_ge _ _ 1 _ _)

theorem spec_zdigits_pos : ∀ (r : Radix) (n : Int), n ≠ 0 →
    0 < Flocq.zdigits r n := by
  intro r n hn
  simp only [Flocq.zdigits, hn, ↓reduceIte, Flocq.zdigitsAux]
  exact lt_of_lt_of_le (by omega) (digitsAux_ge _ _ 1 _ _)

private theorem digitsAux_bounds (a b : Int) (hb : 2 ≤ b) (fuel d : Nat)
    (hd : 0 < d) (hlo : b ^ (d - 1) ≤ a) (hcap : a < b ^ (d + fuel)) :
    ∃ D : Nat, zdigitsAuxCore a b d (b ^ d) fuel = (D : Int) ∧
      d ≤ D ∧ a < b ^ D ∧ b ^ (D - 1) ≤ a := by
  induction fuel generalizing d with
  | zero => exact ⟨d, rfl, le_refl _, by simpa using hcap, hlo⟩
  | succ fuel ih =>
    simp only [zdigitsAuxCore]
    split
    · rename_i h
      exact ⟨d, rfl, le_refl _, h, hlo⟩
    · rename_i h
      have hp : b * b ^ d = b ^ (d + 1) := by rw [pow_succ]; ring
      rw [hp]
      have hcap' : a < b ^ (d + 1 + fuel) := by
        convert hcap using 1 <;> congr 1 <;> omega
      obtain ⟨D, heq, hD, hu, hl⟩ := ih (d + 1) (by omega) (by simpa using (le_of_not_gt h)) hcap'
      refine ⟨D, ?_, by omega, hu, hl⟩
      simpa using heq

private theorem radix_pow_grows (b : Int) (hb : 2 ≤ b) (n : Nat) :
    (n : Int) < b ^ (n + 1) := by
  induction n with
  | zero => simpa using (lt_of_lt_of_le (by norm_num : (0 : Int) < 2) hb)
  | succ n ih =>
    rw [pow_succ]
    have hp : 0 < b ^ (n + 1) := pow_pos (by omega) _
    push_cast
    nlinarith

private theorem zdigits_bounds (r : Radix) (n : Int) (hn : n ≠ 0) :
    ∃ D : Nat, Flocq.zdigits r n = (D : Int) ∧
      0 < D ∧ (n.natAbs : Int) < r.val ^ D ∧ r.val ^ (D - 1) ≤ n.natAbs := by
  have hlo : r.val ^ (1 - 1 : Nat) ≤ (n.natAbs : Int) := by
    simp only [Nat.sub_self, pow_zero]
    exact_mod_cast Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hn)
  have hcap : (n.natAbs : Int) < r.val ^ (1 + (n.natAbs + 1)) := by
    have h := radix_pow_grows r.val r.h (n.natAbs + 1)
    convert lt_trans (by omega : (n.natAbs : Int) < ((n.natAbs + 1 : Nat) : Int)) h using 1 <;>
      congr 1 <;> omega
  obtain ⟨D, heq, hD, hu, hl⟩ := digitsAux_bounds (n.natAbs : Int) r.val r.h (n.natAbs + 1) 1 (by omega) hlo hcap
  refine ⟨D, ?_, by omega, hu, hl⟩
  simpa only [Flocq.zdigits, hn, ↓reduceIte, Flocq.zdigitsAux, pow_one] using heq

theorem spec_zdigits_correct_upper : ∀ (r : Radix) (n : Int),
    n.natAbs < r.val.natAbs ^ (Flocq.zdigits r n).natAbs := by
  intro r n
  by_cases hn : n = 0
  · subst n
    simp [Flocq.zdigits]
  · obtain ⟨D, heq, hD, hu, hl⟩ := zdigits_bounds r n hn
    rw [heq, Int.natAbs_natCast]
    have hr : (r.val.natAbs : Int) = r.val := by rw [Int.natCast_natAbs, abs_of_nonneg (by have := r.h; omega)]
    exact_mod_cast (by simpa only [hr, Int.natCast_pow] using hu :
      (n.natAbs : Int) < (r.val.natAbs : Int) ^ D)

theorem spec_zdigits_correct_lower : ∀ (r : Radix) (n : Int), n ≠ 0 →
    r.val.natAbs ^ ((Flocq.zdigits r n).natAbs - 1) ≤ n.natAbs := by
  intro r n hn
  obtain ⟨D, heq, hD, hu, hl⟩ := zdigits_bounds r n hn
  rw [heq, Int.natAbs_natCast]
  have hr : (r.val.natAbs : Int) = r.val := by rw [Int.natCast_natAbs, abs_of_nonneg (by have := r.h; omega)]
  exact_mod_cast (by simpa only [hr, Int.natCast_pow] using hl :
    (r.val.natAbs : Int) ^ (D - 1) ≤ (n.natAbs : Int))

end FlocqCertificates

#print axioms FlocqCertificates.spec_zdigits_nonneg
#print axioms FlocqCertificates.spec_zdigits_pos
#print axioms FlocqCertificates.spec_zdigits_correct_upper
#print axioms FlocqCertificates.spec_zdigits_correct_lower
