import DedekindReals.Impl.Cut
import DedekindReals.Impl.Additive

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# DedekindReals.Impl.Multiplication

Multiplication and inverse for Dedekind cuts, with frozen rational-bound
vocabulary translated from the Coq `Multiplication` module.

DO NOT MODIFY types or signatures -- these are the fixed vocabulary.
Implement only the function bodies.
-/

namespace DedekindReals

-- !benchmark @start global_aux


-- !benchmark @end global_aux

-- Frozen helpers translated from the Coq multiplication development.

def Qmin4 (a b c d : Rat) : Rat := min (min a b) (min c d)

def Qmax4 (a b c d : Rat) : Rat := max (max a b) (max c d)

def mult_upper (x y : R) (q : Rat) : Prop :=
  ∃ a b c d : Rat,
    x.lower a ∧ x.upper b ∧ y.lower c ∧ y.upper d ∧
      Qmax4 (a * c) (a * d) (b * c) (b * d) < q

def mult_lower (x y : R) (q : Rat) : Prop :=
  ∃ a b c d : Rat,
    x.lower a ∧ x.upper b ∧ y.lower c ∧ y.upper d ∧
      q < Qmin4 (a * c) (a * d) (b * c) (b * d)

def Qmin4_opp : Prop :=
  ∀ a b c d : Rat, Qmin4 (-a) (-b) (-c) (-d) = -Qmax4 a b c d

def Qmax4_opp : Prop :=
  ∀ a b c d : Rat, Qmax4 (-a) (-b) (-c) (-d) = -Qmin4 a b c d

def Qpos_above_opp : Prop := ∀ q : Rat, (0 < q) ↔ (-q < q)

def Qmin4_le_max4 : Prop := ∀ a b c d : Rat, Qmin4 a b c d ≤ Qmax4 a b c d

def Qmin4_flip : Prop := ∀ a b c d : Rat, Qmin4 a b c d = Qmin4 a c b d

def Qmax4_flip : Prop := ∀ a b c d : Rat, Qmax4 a b c d = Qmax4 a c b d

def plus_max4_distr_l : Prop :=
  ∀ n m i j p : Rat, Qmax4 (p + n) (p + m) (p + i) (p + j) = p + Qmax4 n m i j

def plus_min4_distr_l : Prop :=
  ∀ n m i j p : Rat, Qmin4 (p + n) (p + m) (p + i) (p + j) = p + Qmin4 n m i j

def mult_lower_proper : Prop :=
  ∀ x y : R, ∀ q r : Rat, q = r → (mult_lower x y q ↔ mult_lower x y r)

def mult_improve_left_bound : Prop :=
  ∀ a b c d e : Rat, (c < d) → (e < b) → (a ≤ e) →
    Qmin4 (a * c) (a * d) (b * c) (b * d) ≤
      Qmin4 (e * c) (e * d) (b * c) (b * d)

def mult_improve_right_bound : Prop :=
  ∀ a b c d e : Rat, (c < d) → (a < e) → (e ≤ b) →
    Qmax4 (a * c) (a * d) (e * c) (e * d) ≤
      Qmax4 (a * c) (a * d) (b * c) (b * d)

def mult_improve_left_bound_reverse : Prop :=
  ∀ a b c d e : Rat, (c < d) → (a < e) → (e ≤ b) →
    Qmin4 (a * c) (a * d) (b * c) (b * d) ≤
      Qmin4 (a * c) (a * d) (e * c) (e * d)

def mult_improve_right_bound_reverse : Prop :=
  ∀ a b c d e : Rat, (c < d) → (e < b) → (a ≤ e) →
    Qmax4 (e * c) (e * d) (b * c) (b * d) ≤
      Qmax4 (a * c) (a * d) (b * c) (b * d)

def mult_improve_both_bounds : Prop :=
  ∀ a b c d e f : Rat, (e < f) → (c < d) → (a ≤ e) → (f ≤ b) →
    (Qmin4 (a * c) (a * d) (b * c) (b * d) ≤
        Qmin4 (e * c) (e * d) (f * c) (f * d)) ∧
      (Qmax4 (e * c) (e * d) (f * c) (f * d) ≤
        Qmax4 (a * c) (a * d) (b * c) (b * d))

def DReal_mult_disjoint : Prop :=
  ∀ (x y : R) (q : Rat), ¬ (mult_lower x y q ∧ mult_upper x y q)

def DReal_bound : Prop := ∀ x : R, ∃ q : Rat, x.upper q ∧ (Ropp x).upper q

def DReal_mult_maj_base : Prop :=
  ∀ x y p : Rat, (0 ≤ p) →
    Qmax4 0 x y (x + y + p) - Qmin4 0 x y (x + y + p) ≤ Rat.abs x + Rat.abs y + p

def DReal_mult_maj : Prop :=
  ∀ (a b e : Rat), (0 ≤ e) →
    Qmax4 (a * b) (a * (b + e)) ((a + e) * b) ((a + e) * (b + e)) -
        Qmin4 (a * b) (a * (b + e)) ((a + e) * b) ((a + e) * (b + e)) ≤
      (Rat.abs a + Rat.abs b + e) * e

def DReal_mult_located : Prop :=
  ∀ (x y : R) (q r : Rat), (q < r) → mult_lower x y q ∨ mult_upper x y r

def shrink_factor : Prop :=
  ∀ a b : Rat, a < b → ∃ q : Rat, 0 < q ∧ q < 1 ∧ a < q * b

def expand_factor : Prop :=
  ∀ a b : Rat, a < b → ∃ q : Rat, 1 < q ∧ a < q * b

def Qmul_min_distr_l : Prop :=
  ∀ n m p : Rat, 0 ≤ p → min (p * n) (p * m) = p * min n m

def split_pos : Prop :=
  ∀ x : R, ∃ a b : R, Req x (Rminus a b) ∧ Rlt (R_of_Q 0) a ∧ Rlt (R_of_Q 0) b

def inv_lower (x : R) (q : Rat) : Prop :=
  (∃ r : Rat, r < 0 ∧ x.upper r ∧ 1 < q * r) ∨
    (∃ r : Rat, x.lower 0 ∧ x.upper r ∧ q * r < 1)

def inv_upper (x : R) (q : Rat) : Prop :=
  (∃ r : Rat, x.lower r ∧ x.upper 0 ∧ q * r < 1) ∨
    (∃ r : Rat, 0 < r ∧ x.lower r ∧ 1 < q * r)

def inv_lower_pos : Prop :=
  ∀ (x : R) (q : Rat), Rlt (R_of_Q 0) x →
    (inv_lower x q ↔ (∃ r : Rat, x.upper r ∧ q * r < 1))

def inv_upper_pos : Prop :=
  ∀ (x : R) (q : Rat), Rlt (R_of_Q 0) x →
    (inv_upper x q ↔ (∃ r : Rat, 0 < r ∧ x.lower r ∧ 1 < q * r))

def inv_neg_lower_bound : Prop :=
  ∀ x : R, Rlt x (R_of_Q 0) → ∃ l : Rat, inv_lower x l

def inv_pos_lower_bound : Prop :=
  ∀ x : R, Rlt (R_of_Q 0) x → ∃ l : Rat, inv_lower x l

def inv_lower_opp : Prop :=
  ∀ (x : R) (q : Rat), inv_lower (Ropp x) q ↔ inv_upper x (-q)

def inv_upper_opp : Prop :=
  ∀ (x : R) (q : Rat), inv_upper (Ropp x) q ↔ inv_lower x (-q)

def inv_located_pos : Prop :=
  ∀ (x : R) (q r : Rat), Rlt (R_of_Q 0) x → q < r → inv_lower x q ∨ inv_upper x r

def inv_lower_proper : Prop :=
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q = r → (inv_lower x q ↔ inv_lower x r)

def inv_upper_proper : Prop :=
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q = r → (inv_upper x q ↔ inv_upper x r)

def inv_disjoint_pos : Prop :=
  ∀ (x : R) (q : Rat), Rlt (R_of_Q 0) x → ¬ (inv_lower x q ∧ inv_upper x q)

def inv_located : Prop :=
  ∀ (x : R) (q r : Rat), Rneq x (R_of_Q 0) → q < r → inv_lower x q ∨ inv_upper x r

def inv_lower_interval_pos : Prop :=
  ∀ (x : R) (q r : Rat), Rlt (R_of_Q 0) x → q < r → inv_lower x r → inv_lower x q

def inv_upper_interval_pos : Prop :=
  ∀ (x : R) (q r : Rat), Rlt (R_of_Q 0) x → q < r → inv_upper x q → inv_upper x r

def inv_lower_open_pos : Prop :=
  ∀ (x : R) (q : Rat), Rlt (R_of_Q 0) x →
    inv_lower x q → ∃ r : Rat, q < r ∧ inv_lower x r

def inv_upper_open_pos : Prop :=
  ∀ (x : R) (r : Rat), Rlt (R_of_Q 0) x →
    inv_upper x r → ∃ q : Rat, q < r ∧ inv_upper x q

-- API signatures

abbrev RmultSig := R → R → R
abbrev RinvSig := (x : R) → Rneq x (R_of_Q 0) → R

end DedekindReals

-- Reference implementations

namespace DedekindReals
namespace DedekindClosureSupport
open DedekindReals

theorem rectangle_bounds (a b c d t u : Rat) (hat : a ≤ t) (htb : t ≤ b)
    (hcu : c ≤ u) (hud : u ≤ d) :
    Qmin4 (a*c) (a*d) (b*c) (b*d) ≤ t*u ∧
      t*u ≤ Qmax4 (a*c) (a*d) (b*c) (b*d) := by
  have hminac : Qmin4 (a*c) (a*d) (b*c) (b*d) ≤ a*c := by simp [Qmin4]
  have hminad : Qmin4 (a*c) (a*d) (b*c) (b*d) ≤ a*d := by simp [Qmin4]
  have hminbc : Qmin4 (a*c) (a*d) (b*c) (b*d) ≤ b*c := by simp [Qmin4]
  have hminbd : Qmin4 (a*c) (a*d) (b*c) (b*d) ≤ b*d := by simp [Qmin4]
  have hmaxac : a*c ≤ Qmax4 (a*c) (a*d) (b*c) (b*d) := by simp [Qmax4]
  have hmaxad : a*d ≤ Qmax4 (a*c) (a*d) (b*c) (b*d) := by simp [Qmax4]
  have hmaxbc : b*c ≤ Qmax4 (a*c) (a*d) (b*c) (b*d) := by simp [Qmax4]
  have hmaxbd : b*d ≤ Qmax4 (a*c) (a*d) (b*c) (b*d) := by simp [Qmax4]
  constructor
  · by_cases ht : 0 ≤ t
    · have htc : t*c ≤ t*u := mul_le_mul_of_nonneg_left hcu ht
      by_cases hc : 0 ≤ c
      · have := mul_le_mul_of_nonneg_right hat hc; linarith
      · have := mul_le_mul_of_nonpos_right htb (le_of_not_ge hc); linarith
    · have htd : t*d ≤ t*u := mul_le_mul_of_nonpos_left hud (le_of_not_ge ht)
      by_cases hd : 0 ≤ d
      · have := mul_le_mul_of_nonneg_right hat hd; linarith
      · have := mul_le_mul_of_nonpos_right htb (le_of_not_ge hd); linarith
  · by_cases ht : 0 ≤ t
    · have htd : t*u ≤ t*d := mul_le_mul_of_nonneg_left hud ht
      by_cases hd : 0 ≤ d
      · have := mul_le_mul_of_nonneg_right htb hd; linarith
      · have := mul_le_mul_of_nonpos_right hat (le_of_not_ge hd); linarith
    · have htc : t*u ≤ t*c := mul_le_mul_of_nonpos_left hcu (le_of_not_ge ht)
      by_cases hc : 0 ≤ c
      · have := mul_le_mul_of_nonneg_right htb hc; linarith
      · have := mul_le_mul_of_nonpos_right hat (le_of_not_ge hc); linarith

theorem product_distance (a c s t M eps : Rat)
    (hs : |s| ≤ M) (hc : |c| ≤ M) (heps : 0 ≤ eps)
    (hsa : |s-a| ≤ eps) (htc : |t-c| ≤ eps) :
    |s*t-a*c| ≤ 2*M*eps := by
  calc
    |s*t-a*c| = |s*(t-c)+c*(s-a)| := by congr 1; ring
    _ ≤ |s*(t-c)| + |c*(s-a)| := abs_add_le _ _
    _ = |s| * |t-c| + |c| * |s-a| := by rw [abs_mul,abs_mul]
    _ ≤ M*eps+M*eps := add_le_add
      (mul_le_mul hs htc (abs_nonneg _) (le_trans (abs_nonneg _) hs))
      (mul_le_mul hc hsa (abs_nonneg _) (le_trans (abs_nonneg _) hc))
    _ = 2*M*eps := by ring

theorem locate_mult (x y : R) (eta : Rat) (heta : 0 < eta) :
    ∃ eps a c : Rat, 0 < eps ∧ x.lower a ∧ x.upper (a+eps) ∧
      y.lower c ∧ y.upper (c+eps) ∧
      Qmax4 (a*c) (a*(c+eps)) ((a+eps)*c) ((a+eps)*(c+eps)) -
        Qmin4 (a*c) (a*(c+eps)) ((a+eps)*c) ((a+eps)*(c+eps)) < eta := by
  obtain ⟨lx,hlx⟩ := x.lower_bound
  obtain ⟨ux,hux⟩ := x.upper_bound
  obtain ⟨ly,hly⟩ := y.lower_bound
  obtain ⟨uy,huy⟩ := y.upper_bound
  let M := |lx|+|ux|+|ly|+|uy|+2
  have hM : 0 < M := by dsimp [M]; positivity
  let eps := min (1/2 : Rat) (eta/(8*M))
  have heps : 0 < eps := by dsimp [eps]; exact lt_min (by norm_num) (div_pos heta (by positivity))
  have heps1 : eps < 1 := by have := min_le_left (1/2 : Rat) (eta/(8*M)); dsimp [eps]; linarith
  have hepsEta : 4*M*eps < eta := by
    have h := min_le_right (1/2 : Rat) (eta/(8*M))
    have h' : eps*(8*M) ≤ eta := (le_div_iff₀ (by positivity)).mp h
    nlinarith
  obtain ⟨a,b,ha,hb,hab⟩ := straddle x eps heps
  obtain ⟨c,d,hc,hd,hcd⟩ := straddle y eps heps
  have hxlo := lower_upper x hlx hb
  have hxup := lower_upper x ha hux
  have hylo := lower_upper y hly hd
  have hyup := lower_upper y hc huy
  have hux' := le_abs_self ux
  have hlx' := neg_abs_le lx
  have huy' := le_abs_self uy
  have hly' := neg_abs_le ly
  have hlx0 := abs_nonneg lx
  have hux0 := abs_nonneg ux
  have hly0 := abs_nonneg ly
  have huy0 := abs_nonneg uy
  have haM : |a| ≤ M := by apply abs_le.mpr; dsimp [M]; constructor <;> linarith
  have hbM : |a+eps| ≤ M := by apply abs_le.mpr; dsimp [M]; constructor <;> linarith
  have hcM : |c| ≤ M := by apply abs_le.mpr; dsimp [M]; constructor <;> linarith
  have hdM : |c+eps| ≤ M := by apply abs_le.mpr; dsimp [M]; constructor <;> linarith
  have hxe : x.upper (a+eps) := x.upper_upper b _ (by linarith) hb
  have hye : y.upper (c+eps) := y.upper_upper d _ (by linarith) hd
  have h0 : |(0:Rat)| ≤ eps := by simpa using le_of_lt heps
  have h1 : |eps| ≤ eps := by rw [abs_of_pos heps]
  have hac := product_distance a c a c M eps haM hcM (le_of_lt heps) (by simpa using h0) (by simpa using h0)
  have had := product_distance a c a (c+eps) M eps haM hcM (le_of_lt heps) (by simpa using h0) (by simpa using h1)
  have hbc := product_distance a c (a+eps) c M eps hbM hcM (le_of_lt heps) (by simpa using h1) (by simpa using h0)
  have hbd := product_distance a c (a+eps) (c+eps) M eps hbM hcM (le_of_lt heps) (by simpa using h1) (by simpa using h1)
  have hlo : a*c-2*M*eps ≤ Qmin4 (a*c) (a*(c+eps)) ((a+eps)*c) ((a+eps)*(c+eps)) := by
    apply le_min <;> apply le_min
    all_goals first | linarith [(abs_le.mp hac).1] | linarith [(abs_le.mp had).1] | linarith [(abs_le.mp hbc).1] | linarith [(abs_le.mp hbd).1]
  have hup : Qmax4 (a*c) (a*(c+eps)) ((a+eps)*c) ((a+eps)*(c+eps)) ≤ a*c+2*M*eps := by
    apply max_le <;> apply max_le
    all_goals first | linarith [(abs_le.mp hac).2] | linarith [(abs_le.mp had).2] | linarith [(abs_le.mp hbc).2] | linarith [(abs_le.mp hbd).2]
  exact ⟨eps,a,c,heps,ha,hxe,hc,hye,by linarith⟩

end DedekindClosureSupport
end DedekindReals

-- !benchmark @start code_aux def=Rmult

-- !benchmark @end code_aux def=Rmult
namespace DedekindReals
open DedekindClosureSupport

theorem Rmult_lower_bound :
  ∀ x y : R, ∃ q : Rat, mult_lower x y q := by
  intro x y
  obtain ⟨a, ha⟩ := x.lower_bound
  obtain ⟨b, hb⟩ := x.upper_bound
  obtain ⟨c, hc⟩ := y.lower_bound
  obtain ⟨d, hd⟩ := y.upper_bound
  exact ⟨Qmin4 (a*c) (a*d) (b*c) (b*d) - 1, a, b, c, d, ha, hb, hc, hd, by linarith⟩

theorem Rmult_upper_bound :
  ∀ x y : R, ∃ q : Rat, mult_upper x y q := by
  intro x y
  obtain ⟨a, ha⟩ := x.lower_bound
  obtain ⟨b, hb⟩ := x.upper_bound
  obtain ⟨c, hc⟩ := y.lower_bound
  obtain ⟨d, hd⟩ := y.upper_bound
  exact ⟨Qmax4 (a*c) (a*d) (b*c) (b*d) + 1, a, b, c, d, ha, hb, hc, hd, by linarith⟩

theorem Rmult_lower_open :
  ∀ (x y : R) (q : Rat), mult_lower x y q → ∃ r : Rat, q < r ∧ mult_lower x y r := by
  intro x y q h
  obtain ⟨a,b,c,d,ha,hb,hc,hd,h⟩ := h
  exact ⟨(q + Qmin4 (a*c) (a*d) (b*c) (b*d)) / 2, by linarith,
    a,b,c,d,ha,hb,hc,hd,by linarith⟩

theorem Rmult_upper_open :
  ∀ (x y : R) (q : Rat), mult_upper x y q → ∃ r : Rat, r < q ∧ mult_upper x y r := by
  intro x y q h
  obtain ⟨a,b,c,d,ha,hb,hc,hd,h⟩ := h
  exact ⟨(q + Qmax4 (a*c) (a*d) (b*c) (b*d)) / 2, by linarith,
    a,b,c,d,ha,hb,hc,hd,by linarith⟩

theorem Rmult_disjoint :
  ∀ (x y : R) (q : Rat), ¬ (mult_lower x y q ∧ mult_upper x y q) := by
  intro x y q
  rintro ⟨⟨a,b,c,d,ha,hb,hc,hd,hlo⟩,⟨e,f,g,h,he,hf,hg,hh,hup⟩⟩
  have hab := lower_upper x ha hb
  have haf := lower_upper x ha hf
  have heb := lower_upper x he hb
  have hef := lower_upper x he hf
  have hcd := lower_upper y hc hd
  have hch := lower_upper y hc hh
  have hgd := lower_upper y hg hd
  have hgh := lower_upper y hg hh
  have hl := (rectangle_bounds a b c d (max a e) (max c g)
    (le_max_left _ _) (by apply max_le <;> linarith)
    (le_max_left _ _) (by apply max_le <;> linarith)).1
  have hu := (rectangle_bounds e f g h (max a e) (max c g)
    (le_max_right _ _) (by apply max_le <;> linarith)
    (le_max_right _ _) (by apply max_le <;> linarith)).2
  linarith

theorem Rmult_located :
  ∀ (x y : R) (q r : Rat), q < r → mult_lower x y q ∨ mult_upper x y r := by
  intro x y q r hqr
  obtain ⟨eps,a,c,heps,ha,hb,hc,hd,hgap⟩ := locate_mult x y (r-q) (by linarith)
  by_cases h : q < Qmin4 (a*c) (a*(c+eps)) ((a+eps)*c) ((a+eps)*(c+eps))
  · exact Or.inl ⟨a,a+eps,c,c+eps,ha,hb,hc,hd,h⟩
  · exact Or.inr ⟨a,a+eps,c,c+eps,ha,hb,hc,hd,by linarith⟩

end DedekindReals

def DedekindReals.Rmult : DedekindReals.RmultSig :=
-- !benchmark @start code def=Rmult
  fun x y =>
    { lower := DedekindReals.mult_lower x y
      upper := DedekindReals.mult_upper x y
      lower_proper := by
        intro q r hqr
        cases hqr
        rfl
      upper_proper := by
        intro q r hqr
        cases hqr
        rfl
      lower_bound := DedekindReals.Rmult_lower_bound x y
      upper_bound := DedekindReals.Rmult_upper_bound x y
      lower_lower := by
        intro q r hqr h
        rcases h with ⟨a, b, c, d, hxa, hxb, hyc, hyd, hbound⟩
        exact ⟨a, b, c, d, hxa, hxb, hyc, hyd, by grind⟩
      lower_open := DedekindReals.Rmult_lower_open x y
      upper_upper := by
        intro q r hqr h
        rcases h with ⟨a, b, c, d, hxa, hxb, hyc, hyd, hbound⟩
        exact ⟨a, b, c, d, hxa, hxb, hyc, hyd, by grind⟩
      upper_open := DedekindReals.Rmult_upper_open x y
      disjoint := DedekindReals.Rmult_disjoint x y
      located := DedekindReals.Rmult_located x y }
-- !benchmark @end code def=Rmult

namespace DedekindReals

def Rmult_comp : Prop :=
  ∀ x y u v : R, Req x y → Req u v → Req (Rmult x u) (Rmult y v)

end DedekindReals

-- !benchmark @start code_aux def=Rinv
namespace DedekindReals
namespace DedekindClosureSupport
open DedekindReals

theorem nonzero_sign (x : R) (hx : Rneq x (R_of_Q 0)) : x.upper 0 ∨ x.lower 0 := by
  rcases hx with ⟨q,hx,hq⟩ | ⟨q,hq,hx⟩
  · exact Or.inl (x.upper_upper q 0 hq hx)
  · exact Or.inr (x.lower_lower 0 q hq hx)

theorem inv_lower_opp (x : R) (q : Rat) : inv_lower (Ropp x) q ↔ inv_upper x (-q) := by
  constructor
  · rintro (⟨r,hr,hu,h⟩ | ⟨r,h0,hu,h⟩)
    · exact Or.inr ⟨-r,by linarith,hu,by nlinarith⟩
    · exact Or.inl ⟨-r,hu,by simpa [Ropp] using h0,by nlinarith⟩
  · rintro (⟨r,hl,h0,h⟩ | ⟨r,hr,hl,h⟩)
    · exact Or.inr ⟨-r,by simpa [Ropp] using h0,by simpa [Ropp] using hl,by nlinarith⟩
    · exact Or.inl ⟨-r,by linarith,by simpa [Ropp] using hl,by nlinarith⟩

theorem inv_upper_opp (x : R) (q : Rat) : inv_upper (Ropp x) q ↔ inv_lower x (-q) := by
  constructor
  · rintro (⟨r,hl,h0,h⟩ | ⟨r,hr,hl,h⟩)
    · exact Or.inr ⟨-r,by simpa [Ropp] using h0,hl,by nlinarith⟩
    · exact Or.inl ⟨-r,by linarith,hl,by nlinarith⟩
  · rintro (⟨r,hr,hu,h⟩ | ⟨r,h0,hu,h⟩)
    · exact Or.inr ⟨-r,by linarith,by simpa [Ropp] using hu,by nlinarith⟩
    · exact Or.inl ⟨-r,by simpa [Ropp] using hu,by simpa [Ropp] using h0,by nlinarith⟩

theorem inv_located_positive (x : R) (hp : x.lower 0) (q r : Rat) (hqr : q < r) :
    inv_lower x q ∨ inv_upper x r := by
  by_cases hq : q ≤ 0
  · obtain ⟨s,hs⟩ := x.upper_bound
    have hsp := lower_upper x hp hs
    exact Or.inl (Or.inr ⟨s,hp,hs,by nlinarith⟩)
  · have hqp : 0 < q := by linarith
    have hrp : 0 < r := by linarith
    have hqne : q ≠ 0 := ne_of_gt hqp
    have hrne : r ≠ 0 := ne_of_gt hrp
    have hiq : (1/q)*q = 1 := by field_simp
    have hir : (1/r)*r = 1 := by field_simp
    have hirp : 0 < 1/r := one_div_pos.mpr hrp
    have hip : 1/r < 1/q := by
      exact (one_div_lt_one_div hrp hqp).2 hqr
    let a := (2*(1/r)+1/q)/3
    let b := ((1/r)+2*(1/q))/3
    have hab : a < b := by dsimp [a,b]; linarith
    rcases x.located a b hab with ha | hb
    · right; right
      refine ⟨a,?_,ha,?_⟩
      · dsimp [a]; linarith
      · have hh : r * (1/q) > 1 := by nlinarith
        dsimp [a]; nlinarith
    · left; right
      refine ⟨b,hp,hb,?_⟩
      have hh : q * (1/r) < 1 := by nlinarith
      dsimp [b]; nlinarith

end DedekindClosureSupport
end DedekindReals

namespace DedekindReals
open DedekindClosureSupport

theorem Rinv_lower_proper :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q = r → (inv_lower x q ↔ inv_lower x r) := by
  intro x _hx q r h
  subst q; rfl

theorem Rinv_upper_proper :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q = r → (inv_upper x q ↔ inv_upper x r) := by
  intro x _hx q r h
  subst q; rfl

theorem Rinv_lower_bound :
  ∀ x : R, Rneq x (R_of_Q 0) → ∃ q : Rat, inv_lower x q := by
  intro x hx
  rcases nonzero_sign x hx with hn | hp
  · obtain ⟨r,hr,hu⟩ := x.upper_open 0 hn
    refine ⟨2 / r, Or.inl ⟨r,hr,hu,?_⟩⟩
    have hne : r ≠ 0 := ne_of_lt hr
    field_simp; norm_num
  · obtain ⟨r,hr⟩ := x.upper_bound
    have hrpos := lower_upper x hp hr
    exact ⟨-1, Or.inr ⟨r,hp,hr,by nlinarith⟩⟩

theorem Rinv_upper_bound :
  ∀ x : R, Rneq x (R_of_Q 0) → ∃ q : Rat, inv_upper x q := by
  intro x hx
  rcases nonzero_sign x hx with hn | hp
  · obtain ⟨r,hr⟩ := x.lower_bound
    have hrneg := lower_upper x hr hn
    exact ⟨1, Or.inl ⟨r,hr,hn,by nlinarith⟩⟩
  · obtain ⟨r,hr,hl⟩ := x.lower_open 0 hp
    refine ⟨2 / r, Or.inr ⟨r,hr,hl,?_⟩⟩
    have hne : r ≠ 0 := ne_of_gt hr
    field_simp; norm_num

theorem Rinv_lower_lower :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q < r → inv_lower x r → inv_lower x q := by
  intro x _hx q r hqr h
  rcases h with ⟨s,hs,hu,h⟩ | ⟨s,hl,hu,h⟩
  · exact Or.inl ⟨s,hs,hu,by nlinarith⟩
  · have := lower_upper x hl hu
    exact Or.inr ⟨s,hl,hu,by nlinarith⟩

theorem Rinv_lower_open :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q : Rat, inv_lower x q → ∃ r : Rat, q < r ∧ inv_lower x r := by
  intro x _hx q h
  rcases h with ⟨s,hs,hu,h⟩ | ⟨s,hl,hu,h⟩
  · have hsne : s ≠ 0 := ne_of_lt hs
    have hi : (1/s)*s = 1 := by field_simp
    have hq : q < 1/s := by nlinarith
    refine ⟨(q+1/s)/2, by linarith, Or.inl ⟨s,hs,hu,?_⟩⟩
    nlinarith
  · have hs := lower_upper x hl hu
    have hsne : s ≠ 0 := ne_of_gt hs
    have hi : (1/s)*s = 1 := by field_simp
    have hq : q < 1/s := by nlinarith
    refine ⟨(q+1/s)/2, by linarith, Or.inr ⟨s,hl,hu,?_⟩⟩
    nlinarith

theorem Rinv_upper_upper :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q < r → inv_upper x q → inv_upper x r := by
  intro x _hx q r hqr h
  rcases h with ⟨s,hl,hu,h⟩ | ⟨s,hs,hl,h⟩
  · have := lower_upper x hl hu
    exact Or.inl ⟨s,hl,hu,by nlinarith⟩
  · exact Or.inr ⟨s,hs,hl,by nlinarith⟩

theorem Rinv_upper_open :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ r : Rat, inv_upper x r → ∃ q : Rat, q < r ∧ inv_upper x q := by
  intro x _hx q h
  rcases h with ⟨s,hl,hu,h⟩ | ⟨s,hs,hl,h⟩
  · have hs := lower_upper x hl hu
    have hsne : s ≠ 0 := ne_of_lt hs
    have hi : (1/s)*s = 1 := by field_simp
    have hq : 1/s < q := by nlinarith
    refine ⟨(q+1/s)/2, by linarith, Or.inl ⟨s,hl,hu,?_⟩⟩
    nlinarith
  · have hsne : s ≠ 0 := ne_of_gt hs
    have hi : (1/s)*s = 1 := by field_simp
    have hq : 1/s < q := by nlinarith
    refine ⟨(q+1/s)/2, by linarith, Or.inr ⟨s,hs,hl,?_⟩⟩
    nlinarith

theorem Rinv_disjoint :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q : Rat, ¬ (inv_lower x q ∧ inv_upper x q) := by
  intro x _hx q
  rintro ⟨hl,hu⟩
  rcases hl with ⟨r,hr,hru,hl⟩ | ⟨r,h0,hr,hl⟩
  · rcases hu with ⟨s,hsl,h0,hu⟩ | ⟨s,hs,hsl,hu⟩
    · have hsr := lower_upper x hsl hru
      have hsneg := lower_upper x hsl h0
      have hq : q < 0 := by nlinarith
      nlinarith
    · have := lower_upper x hsl hru
      linarith
  · rcases hu with ⟨s,hsl,h0',hu⟩ | ⟨s,hs,hsl,hu⟩
    · exact x.disjoint 0 ⟨h0,h0'⟩
    · have hsr := lower_upper x hsl hr
      have hrpos := lower_upper x h0 hr
      have hq : 0 < q := by nlinarith
      nlinarith

theorem Rinv_located :
  ∀ x : R, Rneq x (R_of_Q 0) → ∀ q r : Rat, q < r → inv_lower x q ∨ inv_upper x r := by
  intro x hx q r hqr
  rcases nonzero_sign x hx with hn | hp
  · have hp : (Ropp x).lower 0 := by simpa [Ropp] using hn
    rcases inv_located_positive (Ropp x) hp (-r) (-q) (by linarith) with h | h
    · exact Or.inr (by simpa using (DedekindClosureSupport.inv_lower_opp x (-r)).mp h)
    · exact Or.inl (by simpa using (DedekindClosureSupport.inv_upper_opp x (-q)).mp h)
  · exact inv_located_positive x hp q r hqr

end DedekindReals
-- !benchmark @end code_aux def=Rinv


def DedekindReals.Rinv : DedekindReals.RinvSig :=
-- !benchmark @start code def=Rinv
  fun x hx =>
    { lower := DedekindReals.inv_lower x
      upper := DedekindReals.inv_upper x
      lower_proper := DedekindReals.Rinv_lower_proper x hx
      upper_proper := DedekindReals.Rinv_upper_proper x hx
      lower_bound := DedekindReals.Rinv_lower_bound x hx
      upper_bound := DedekindReals.Rinv_upper_bound x hx
      lower_lower := DedekindReals.Rinv_lower_lower x hx
      lower_open := DedekindReals.Rinv_lower_open x hx
      upper_upper := DedekindReals.Rinv_upper_upper x hx
      upper_open := DedekindReals.Rinv_upper_open x hx
      disjoint := DedekindReals.Rinv_disjoint x hx
      located := DedekindReals.Rinv_located x hx }
-- !benchmark @end code def=Rinv
