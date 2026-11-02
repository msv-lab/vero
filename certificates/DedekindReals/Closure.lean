import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import DedekindReals.Impl.Multiplication
import DedekindReals.Impl.Archimedean

set_option maxHeartbeats 800000
namespace DedekindCertificates
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

theorem plus_lower_bound (x y : R) :
    ∃ q : Rat, ∃ r s : Rat, q < r + s ∧ x.lower r ∧ y.lower s := by
  obtain ⟨r, hr⟩ := x.lower_bound
  obtain ⟨s, hs⟩ := y.lower_bound
  exact ⟨r + s - 1, r, s, by linarith, hr, hs⟩

theorem plus_upper_bound (x y : R) :
    ∃ q : Rat, ∃ r s : Rat, r + s < q ∧ x.upper r ∧ y.upper s := by
  obtain ⟨r, hr⟩ := x.upper_bound
  obtain ⟨s, hs⟩ := y.upper_bound
  exact ⟨r + s + 1, r, s, by linarith, hr, hs⟩

theorem plus_lower_open (x y : R) (q : Rat)
    (h : ∃ r s : Rat, q < r + s ∧ x.lower r ∧ y.lower s) :
    ∃ r : Rat, q < r ∧ ∃ u v : Rat, r < u + v ∧ x.lower u ∧ y.lower v := by
  obtain ⟨r, s, h, hr, hs⟩ := h
  exact ⟨(q + (r + s)) / 2, by linarith, r, s, by linarith, hr, hs⟩

theorem plus_upper_open (x y : R) (q : Rat)
    (h : ∃ r s : Rat, r + s < q ∧ x.upper r ∧ y.upper s) :
    ∃ r : Rat, r < q ∧ ∃ u v : Rat, u + v < r ∧ x.upper u ∧ y.upper v := by
  obtain ⟨r, s, h, hr, hs⟩ := h
  exact ⟨(q + (r + s)) / 2, by linarith, r, s, by linarith, hr, hs⟩

theorem plus_disjoint (x y : R) (q : Rat) :
    ¬ ((∃ r s : Rat, q < r + s ∧ x.lower r ∧ y.lower s) ∧
      (∃ r s : Rat, r + s < q ∧ x.upper r ∧ y.upper s)) := by
  rintro ⟨⟨a, b, hab, ha, hb⟩, ⟨c, d, hcd, hc, hd⟩⟩
  have := lower_upper x ha hc
  have := lower_upper y hb hd
  linarith

theorem plus_located (x y : R) (q r : Rat) (hqr : q < r) :
    (∃ u v : Rat, q < u + v ∧ x.lower u ∧ y.lower v) ∨
      (∃ u v : Rat, u + v < r ∧ x.upper u ∧ y.upper v) := by
  obtain ⟨a, b, ha, hb, hab⟩ := straddle x ((r - q) / 3) (by linarith)
  obtain ⟨c, d, hc, hd, hcd⟩ := straddle y ((r - q) / 3) (by linarith)
  by_cases h : q < a + c
  · exact Or.inl ⟨a, c, h, ha, hc⟩
  · exact Or.inr ⟨b, d, by linarith, hb, hd⟩

theorem mult_lower_bound (x y : R) : ∃ q : Rat, mult_lower x y q := by
  obtain ⟨a, ha⟩ := x.lower_bound
  obtain ⟨b, hb⟩ := x.upper_bound
  obtain ⟨c, hc⟩ := y.lower_bound
  obtain ⟨d, hd⟩ := y.upper_bound
  exact ⟨Qmin4 (a*c) (a*d) (b*c) (b*d) - 1, a, b, c, d, ha, hb, hc, hd, by linarith⟩

theorem mult_upper_bound (x y : R) : ∃ q : Rat, mult_upper x y q := by
  obtain ⟨a, ha⟩ := x.lower_bound
  obtain ⟨b, hb⟩ := x.upper_bound
  obtain ⟨c, hc⟩ := y.lower_bound
  obtain ⟨d, hd⟩ := y.upper_bound
  exact ⟨Qmax4 (a*c) (a*d) (b*c) (b*d) + 1, a, b, c, d, ha, hb, hc, hd, by linarith⟩

theorem mult_lower_open (x y : R) (q : Rat) (h : mult_lower x y q) :
    ∃ r : Rat, q < r ∧ mult_lower x y r := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,h⟩ := h
  exact ⟨(q + Qmin4 (a*c) (a*d) (b*c) (b*d)) / 2, by linarith,
    a,b,c,d,ha,hb,hc,hd,by linarith⟩

theorem mult_upper_open (x y : R) (q : Rat) (h : mult_upper x y q) :
    ∃ r : Rat, r < q ∧ mult_upper x y r := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,h⟩ := h
  exact ⟨(q + Qmax4 (a*c) (a*d) (b*c) (b*d)) / 2, by linarith,
    a,b,c,d,ha,hb,hc,hd,by linarith⟩

theorem inv_lower_proper (x : R) (_hx : Rneq x (R_of_Q 0)) (q r : Rat) (h : q = r) :
    inv_lower x q ↔ inv_lower x r := by subst q; rfl

theorem inv_upper_proper (x : R) (_hx : Rneq x (R_of_Q 0)) (q r : Rat) (h : q = r) :
    inv_upper x q ↔ inv_upper x r := by subst q; rfl

theorem nonzero_sign (x : R) (hx : Rneq x (R_of_Q 0)) : x.upper 0 ∨ x.lower 0 := by
  rcases hx with ⟨q,hx,hq⟩ | ⟨q,hq,hx⟩
  · exact Or.inl (x.upper_upper q 0 hq hx)
  · exact Or.inr (x.lower_lower 0 q hq hx)

theorem inv_lower_bound (x : R) (hx : Rneq x (R_of_Q 0)) : ∃ q : Rat, inv_lower x q := by
  rcases nonzero_sign x hx with hn | hp
  · obtain ⟨r,hr,hu⟩ := x.upper_open 0 hn
    refine ⟨2 / r, Or.inl ⟨r,hr,hu,?_⟩⟩
    have hne : r ≠ 0 := ne_of_lt hr
    field_simp; norm_num
  · obtain ⟨r,hr⟩ := x.upper_bound
    have hrpos := lower_upper x hp hr
    exact ⟨-1, Or.inr ⟨r,hp,hr,by nlinarith⟩⟩

theorem inv_upper_bound (x : R) (hx : Rneq x (R_of_Q 0)) : ∃ q : Rat, inv_upper x q := by
  rcases nonzero_sign x hx with hn | hp
  · obtain ⟨r,hr⟩ := x.lower_bound
    have hrneg := lower_upper x hr hn
    exact ⟨1, Or.inl ⟨r,hr,hn,by nlinarith⟩⟩
  · obtain ⟨r,hr,hl⟩ := x.lower_open 0 hp
    refine ⟨2 / r, Or.inr ⟨r,hr,hl,?_⟩⟩
    have hne : r ≠ 0 := ne_of_gt hr
    field_simp; norm_num

theorem inv_lower_lower (x : R) (_hx : Rneq x (R_of_Q 0)) (q r : Rat) (hqr : q < r)
    (h : inv_lower x r) : inv_lower x q := by
  rcases h with ⟨s,hs,hu,h⟩ | ⟨s,hl,hu,h⟩
  · exact Or.inl ⟨s,hs,hu,by nlinarith⟩
  · have := lower_upper x hl hu
    exact Or.inr ⟨s,hl,hu,by nlinarith⟩

theorem inv_upper_upper (x : R) (_hx : Rneq x (R_of_Q 0)) (q r : Rat) (hqr : q < r)
    (h : inv_upper x q) : inv_upper x r := by
  rcases h with ⟨s,hl,hu,h⟩ | ⟨s,hs,hl,h⟩
  · have := lower_upper x hl hu
    exact Or.inl ⟨s,hl,hu,by nlinarith⟩
  · exact Or.inr ⟨s,hs,hl,by nlinarith⟩

theorem inv_lower_open (x : R) (_hx : Rneq x (R_of_Q 0)) (q : Rat) (h : inv_lower x q) :
    ∃ r : Rat, q < r ∧ inv_lower x r := by
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

theorem inv_upper_open (x : R) (_hx : Rneq x (R_of_Q 0)) (q : Rat) (h : inv_upper x q) :
    ∃ r : Rat, r < q ∧ inv_upper x r := by
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

theorem inv_disjoint (x : R) (_hx : Rneq x (R_of_Q 0)) (q : Rat) :
    ¬(inv_lower x q ∧ inv_upper x q) := by
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

theorem inv_located (x : R) (hx : Rneq x (R_of_Q 0)) (q r : Rat) (hqr : q < r) :
    inv_lower x q ∨ inv_upper x r := by
  rcases nonzero_sign x hx with hn | hp
  · have hp : (Ropp x).lower 0 := by simpa [Ropp] using hn
    rcases inv_located_positive (Ropp x) hp (-r) (-q) (by linarith) with h | h
    · exact Or.inr (by simpa using (inv_lower_opp x (-r)).mp h)
    · exact Or.inl (by simpa using (inv_upper_opp x (-q)).mp h)
  · exact inv_located_positive x hp q r hqr

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

theorem mult_disjoint (x y : R) (q : Rat) : ¬(mult_lower x y q ∧ mult_upper x y q) := by
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

theorem mult_located (x y : R) (q r : Rat) (hqr : q < r) :
    mult_lower x y q ∨ mult_upper x y r := by
  obtain ⟨eps,a,c,heps,ha,hb,hc,hd,hgap⟩ := locate_mult x y (r-q) (by linarith)
  by_cases h : q < Qmin4 (a*c) (a*(c+eps)) ((a+eps)*c) ((a+eps)*(c+eps))
  · exact Or.inl ⟨a,a+eps,c,c+eps,ha,hb,hc,hd,h⟩
  · exact Or.inr ⟨a,a+eps,c,c+eps,ha,hb,hc,hd,by linarith⟩

end DedekindCertificates
