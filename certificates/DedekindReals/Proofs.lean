import Closure
import DedekindReals.Spec.Cut
import DedekindReals.Spec.Order
import DedekindReals.Spec.MinMax
import DedekindReals.Spec.MiscLemmas
import DedekindReals.Spec.Cauchy
import DedekindReals.Spec.Completeness
import DedekindReals.Spec.DecOrder
import DedekindReals.Spec.Archimedean
import DedekindReals.Spec.Multiplication
import DedekindReals.Spec.Additive

namespace DedekindCertificates
open DedekindReals

theorem le_upper_iff (x y : R) : Rle x y ↔ Rle_upper x y := by
  constructor
  · intro h q hq
    obtain ⟨r, hrq, hr⟩ := y.upper_open q hq
    rcases x.located r q hrq with hx | hx
    · exact False.elim (y.disjoint r ⟨h r hx, hr⟩)
    · exact hx
  · intro h q hq
    obtain ⟨r, hqr, hr⟩ := x.lower_open q hq
    rcases y.located q r hqr with hy | hy
    · exact hy
    · exact False.elim (x.disjoint r ⟨hr, h r hy⟩)

theorem not_lt_iff (x y : R) : ¬Rlt x y ↔ Rle y x := by
  constructor
  · intro h q hq
    obtain ⟨r, hqr, hr⟩ := y.lower_open q hq
    rcases x.located q r hqr with hx | hx
    · exact hx
    · exact False.elim (h ⟨r, hx, hr⟩)
  · rintro h ⟨q, hx, hy⟩
    exact x.disjoint q ⟨h q hy, hx⟩

theorem lt_irrefl (x : R) : ¬Rlt x x := by
  rintro ⟨q, hu, hl⟩; exact x.disjoint q ⟨hl,hu⟩

theorem lt_trans (x y z : R) (hxy : Rlt x y) (hyz : Rlt y z) : Rlt x z := by
  obtain ⟨q,hx,hy⟩ := hxy
  obtain ⟨r,hy',hz⟩ := hyz
  exact ⟨q,hx,z.lower_lower q r (lower_upper y hy hy') hz⟩

theorem lt_linear (x y z : R) (hxy : Rlt x y) : Rlt x z ∨ Rlt z y := by
  obtain ⟨q,hx,hy⟩ := hxy
  obtain ⟨r,hr,hxr⟩ := x.upper_open q hx
  rcases z.located r q hr with hz | hz
  · exact Or.inl ⟨r,hxr,hz⟩
  · exact Or.inr ⟨q,hz,hy⟩

theorem spec_Rle_equiv : _root_.spec_Rle_equiv canonical := le_upper_iff
theorem spec_Rnot_lt_le : _root_.spec_Rnot_lt_le canonical := not_lt_iff
theorem spec_Req_equiv : _root_.spec_Req_equiv canonical := by
  intro x y
  exact and_congr (le_upper_iff x y) (le_upper_iff y x)
theorem spec_lower_below_upper : _root_.spec_lower_below_upper canonical := by
  intro x q r hq hr; exact lower_upper x hq hr
theorem spec_lower_le : _root_.spec_lower_le canonical := by
  intro x q r hr hqr; exact lower_le x hqr hr
theorem spec_upper_le : _root_.spec_upper_le canonical := by
  intro x q r hq hqr; exact upper_le x hqr hq
theorem spec_R_lt_Q_iff : _root_.spec_R_lt_Q_iff canonical := by
  intro x q
  constructor
  · intro h
    obtain ⟨r,hr,hxr⟩ := x.upper_open q h
    exact ⟨r,hxr,hr⟩
  · rintro ⟨r,hxr,hr⟩
    exact x.upper_upper r q hr hxr
theorem spec_R_is_Q_iff : _root_.spec_R_is_Q_iff canonical := by
  intro x q
  change Req x (R_of_Q q) ↔ _
  constructor
  · intro h r
    exact ⟨fun hr => (le_upper_iff x (R_of_Q q)).mp h.1 r hr,
      fun hr => h.2 r hr⟩
  · intro h
    constructor
    · intro r hr
      obtain ⟨s, hrs, hs⟩ := x.lower_open r hr
      have hrq : r < q := by
        by_contra hn
        have hqs : q < s := by linarith
        exact x.disjoint s ⟨hs,(h s).1 hqs⟩
      exact hrq
    · intro r hr; exact (h r).2 hr

theorem spec_Rlt_irrefl : _root_.spec_Rlt_irrefl canonical := lt_irrefl
theorem spec_Rlt_trans : _root_.spec_Rlt_trans canonical := lt_trans
theorem spec_Rlt_asymm : _root_.spec_Rlt_asymm canonical := by
  rintro x y ⟨h,h'⟩; exact lt_irrefl x (lt_trans x y x h h')
theorem spec_Rlt_linear : _root_.spec_Rlt_linear canonical := lt_linear
theorem spec_Rneq_symm : _root_.spec_Rneq_symm canonical := by
  intro x y h; exact h.symm
theorem spec_Rneq_irrefl : _root_.spec_Rneq_irrefl canonical := by
  intro x h; exact h.elim (lt_irrefl x) (lt_irrefl x)
theorem spec_Rnew_contrans : _root_.spec_Rnew_contrans canonical := by
  intro x y z h
  rcases h with h | h
  · rcases lt_linear x y z h with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rcases lt_linear y x z h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr h)
theorem spec_Rle_refl : _root_.spec_Rle_refl canonical := by intro x q h; exact h
theorem spec_Rle_trans : _root_.spec_Rle_trans canonical := by
  intro x y z h h' q hq; exact h' q (h q hq)
theorem spec_Rle_antisym : _root_.spec_Rle_antisym canonical := by
  intro x y h h'; exact ⟨h,h'⟩
theorem spec_Rlt_le_weak : _root_.spec_Rlt_le_weak canonical := by
  rintro x y ⟨q,hx,hy⟩ r hr
  exact y.lower_lower r q (lower_upper x hr hx) hy
theorem spec_Order_Rnot_lt_le : _root_.spec_Order_Rnot_lt_le canonical := not_lt_iff
theorem spec_R0_lt_1 : _root_.spec_R0_lt_1 canonical := by
  exact ⟨(1/2 : Rat), by norm_num [canonical,canonicalDedekindReals,R_of_Q], by norm_num [canonical,canonicalDedekindReals,R_of_Q]⟩

theorem spec_Rmin_spec : _root_.spec_Rmin_spec canonical := by
  intro x y z; change (∀ q, z.lower q → x.lower q ∧ y.lower q) ↔ _
  constructor
  · intro h; exact ⟨fun q hq => (h q hq).1, fun q hq => (h q hq).2⟩
  · rintro ⟨h,h'⟩ q hq; exact ⟨h q hq,h' q hq⟩
theorem spec_Rmin_lower_l : _root_.spec_Rmin_lower_l canonical := by
  intro x y q h; exact h.1
theorem spec_Rmin_lower_r : _root_.spec_Rmin_lower_r canonical := by
  intro x y q h; exact h.2
theorem spec_Rmin_idempotent : _root_.spec_Rmin_idempotent canonical := by
  intro x; exact ⟨fun q h => h.1,fun q h => ⟨h,h⟩⟩
theorem spec_Rmin_comm : _root_.spec_Rmin_comm canonical := by
  intro x y; exact ⟨fun q h => h.symm,fun q h => h.symm⟩
theorem spec_Rmin_assoc : _root_.spec_Rmin_assoc canonical := by
  intro x y z; exact ⟨fun q h => ⟨⟨h.1,h.2.1⟩,h.2.2⟩,
    fun q h => ⟨h.1.1,h.1.2,h.2⟩⟩
theorem spec_Rmax_spec : _root_.spec_Rmax_spec canonical := by
  intro x y z
  change (∀ q, x.lower q ∨ y.lower q → z.lower q) ↔ _
  constructor
  · intro h; exact ⟨fun q hq => h q (Or.inl hq),fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨h,h'⟩ q hq; exact hq.elim (h q) (h' q)
theorem spec_Rmax_upper_l : _root_.spec_Rmax_upper_l canonical := by
  intro x y q h; exact Or.inl h
theorem spec_Rmax_upper_r : _root_.spec_Rmax_upper_r canonical := by
  intro x y q h; exact Or.inr h
theorem spec_Rmax_idempotent : _root_.spec_Rmax_idempotent canonical := by
  intro x; exact ⟨fun q h => h.elim id id,fun q h => Or.inl h⟩
theorem spec_Rmax_comm : _root_.spec_Rmax_comm canonical := by
  intro x y; exact ⟨fun q h => h.symm,fun q h => h.symm⟩
theorem spec_Rmax_assoc : _root_.spec_Rmax_assoc canonical := by
  intro x y z
  constructor <;> intro q h
  · exact h.elim (fun h => Or.inl (Or.inl h))
      (fun h => h.elim (fun h => Or.inl (Or.inr h)) Or.inr)
  · exact h.elim (fun h => h.elim Or.inl (fun h => Or.inr (Or.inl h)))
      (fun h => Or.inr (Or.inr h))

theorem spec_lt_from_le_nonzero : _root_.spec_lt_from_le_nonzero canonical := by
  intro p h hn; exact lt_of_le_of_ne h (Ne.symm hn)
theorem spec_pow_Q1_Qle : _root_.spec_pow_Q1_Qle canonical := by
  intro q n h; exact one_le_pow₀ h
theorem spec_pow_Q1_incr : _root_.spec_pow_Q1_incr canonical := by
  intro q n p h hnp; exact pow_le_pow_right₀ h hnp
theorem spec_middle_between : _root_.spec_middle_between canonical := by
  intro q r h; constructor <;> linarith
theorem spec_archimedean : _root_.spec_archimedean canonical := straddle
theorem spec_DecOrderImpliesLPO : _root_.spec_DecOrderImpliesLPO canonical := by
  classical
  intro _ un
  by_cases h : ∃ n, un n = true
  · exact Or.inl h
  · right; intro n; cases hn : un n <;> simp_all
theorem spec_RCut_eq_refl : _root_.spec_RCut_eq_refl canonical := by
  intro c; exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
theorem spec_RCut_eq_sym : _root_.spec_RCut_eq_sym canonical := by
  rintro c d ⟨h,h'⟩; exact ⟨fun x => (h x).symm,fun x => (h' x).symm⟩
theorem spec_RCut_eq_trans : _root_.spec_RCut_eq_trans canonical := by
  rintro c d e ⟨h,h'⟩ ⟨g,g'⟩; exact ⟨fun x => (h x).trans (g x),fun x => (h' x).trans (g' x)⟩
theorem spec_mult_lower_open : _root_.spec_mult_lower_open canonical := mult_lower_open
theorem spec_mult_upper_open : _root_.spec_mult_upper_open canonical := mult_upper_open

theorem spec_DReal_locate_mult : _root_.spec_DReal_locate_mult canonical := locate_mult

theorem spec_Rmult_comm : _root_.spec_Rmult_comm canonical := by
  have comm (x y : R) : Rle (Rmult x y) (Rmult y x) := by
    rintro q ⟨a,b,c,d,ha,hb,hc,hd,h⟩
    refine ⟨c,d,a,b,hc,hd,ha,hb,?_⟩
    simpa only [Qmin4,mul_comm,min_comm,min_left_comm,min_assoc] using h
  intro x y; exact ⟨comm x y,comm y x⟩

theorem spec_Ropp_inv_permute : _root_.spec_Ropp_inv_permute canonical := by
  intro x hx hnx
  constructor
  · intro q hq
    exact (inv_lower_opp x q).mpr hq
  · intro q hq
    exact (inv_lower_opp x q).mp hq

theorem spec_CauchyQ_lower_open : _root_.spec_CauchyQ_lower_open canonical := by
  rintro un q ⟨r,n,hr,h⟩
  refine ⟨q+r/2,by linarith,r/2,n,by linarith,?_⟩
  intro i hi; have := h i hi; linarith
theorem spec_CauchyQ_upper_open : _root_.spec_CauchyQ_upper_open canonical := by
  rintro un q ⟨r,n,hr,h⟩
  refine ⟨q-r/2,by linarith,r/2,n,by linarith,?_⟩
  intro i hi; have := h i hi; linarith
theorem spec_CauchyQ_located : _root_.spec_CauchyQ_located canonical := by
  intro un q r h hqr
  exact (CauchyQ_R un h).located q r hqr
theorem spec_Un_cv_cauchy : _root_.spec_Un_cv_cauchy canonical := by
  intro un l h eps heps
  obtain ⟨n,hn⟩ := h (eps/2) (by linarith)
  refine ⟨n,?_⟩
  intro i j hi hj
  have hi' := hn i hi
  have hj' := hn j hj
  unfold Rat.abs at hi' hj' ⊢
  split at hi' <;> split at hj' <;> split <;> linarith

theorem spec_Ropp_involutive : _root_.spec_Ropp_involutive canonical := by
  intro x
  change Req (Ropp (Ropp x)) x
  constructor <;> intro q h <;> simpa [Ropp] using h

theorem spec_Rplus_comm : _root_.spec_Rplus_comm canonical := by
  have comm (x y : R) : Rle (Rplus x y) (Rplus y x) := by
    rintro q ⟨a,b,h,ha,hb⟩
    exact ⟨b,a,by linarith,hb,ha⟩
  intro x y; exact ⟨comm x y,comm y x⟩

theorem spec_Rplus_0_l : _root_.spec_Rplus_0_l canonical := by
  intro x
  constructor
  · rintro q ⟨a,b,h,ha,hb⟩
    exact x.lower_lower q b (by change a < 0 at ha; linarith) hb
  · intro q hq
    obtain ⟨r,hqr,hr⟩ := x.lower_open q hq
    exact ⟨(q-r)/2,r,by linarith,by change (q-r)/2 < 0; linarith,hr⟩

theorem plus_le_compat (x y z w : R) (hxy : Rle x y) (hzw : Rle z w) :
    Rle (Rplus x z) (Rplus y w) := by
  rintro q ⟨a,b,h,ha,hb⟩
  exact ⟨a,b,h,hxy a ha,hzw b hb⟩

theorem plus_lt_right (x y z : R) : Rlt x y ↔ Rlt (Rplus x z) (Rplus y z) := by
  constructor
  · rintro ⟨t,hx,hy⟩
    obtain ⟨a,hat,ha⟩ := x.upper_open t hx
    obtain ⟨b,htb,hb⟩ := y.lower_open t hy
    obtain ⟨c,d,hc,hd,hcd⟩ := straddle z ((b-a)/2) (by linarith)
    refine ⟨(a+d+b+c)/2,⟨a,d,by linarith,ha,hd⟩,⟨b,c,by linarith,hb,hc⟩⟩
  · rintro ⟨s,⟨a,c,hac,ha,hc⟩,⟨b,d,hbd,hb,hd⟩⟩
    have hdc := lower_upper z hd hc
    have hab : a < b := by linarith
    exact ⟨(a+b)/2,x.upper_upper a _ (by linarith) ha,
      y.lower_lower _ b (by linarith) hb⟩

theorem plus_lt_left (x y z : R) : Rlt y z ↔ Rlt (Rplus x y) (Rplus x z) := by
  constructor
  · intro h
    obtain ⟨s,⟨a,c,hac,ha,hc⟩,⟨b,d,hbd,hb,hd⟩⟩ := (plus_lt_right y z x).mp h
    exact ⟨s,⟨c,a,by linarith,hc,ha⟩,⟨d,b,by linarith,hd,hb⟩⟩
  · rintro ⟨s,⟨a,c,hac,ha,hc⟩,⟨b,d,hbd,hb,hd⟩⟩
    apply (plus_lt_right y z x).mpr
    exact ⟨s,⟨c,a,by linarith,hc,ha⟩,⟨d,b,by linarith,hd,hb⟩⟩

theorem spec_Rplus_lt_compat_r : _root_.spec_Rplus_lt_compat_r canonical := plus_lt_right
theorem spec_Rplus_lt_compat_l : _root_.spec_Rplus_lt_compat_l canonical := plus_lt_left
theorem spec_Rplus_le_compat_l : _root_.spec_Rplus_le_compat_l canonical := by
  intro x y z
  change Rle y z ↔ Rle (Rplus x y) (Rplus x z)
  rw [←not_lt_iff,←not_lt_iff]
  exact not_congr (plus_lt_left x z y)
theorem spec_Rplus_le_compat_r : _root_.spec_Rplus_le_compat_r canonical := by
  intro x y z
  change Rle x y ↔ Rle (Rplus x z) (Rplus y z)
  rw [←not_lt_iff,←not_lt_iff]
  exact not_congr (plus_lt_right y x z)
theorem spec_Order_Rplus_le_compat_l : _root_.spec_Order_Rplus_le_compat_l canonical := spec_Rplus_le_compat_l
theorem spec_Order_Rplus_le_compat_r : _root_.spec_Order_Rplus_le_compat_r canonical := spec_Rplus_le_compat_r
theorem spec_Rplus_lt_reg_l : _root_.spec_Rplus_lt_reg_l canonical := by
  intro x y z; exact (plus_lt_left x y z).mpr
theorem spec_Rplus_lt_reg_r : _root_.spec_Rplus_lt_reg_r canonical := by
  intro x y z; exact (plus_lt_right y z x).mpr

theorem spec_R_of_Q_plus : _root_.spec_R_of_Q_plus canonical := by
  intro p q
  constructor
  · intro r hr
    change r < p+q at hr
    let delta := (p+q-r)/3
    exact ⟨p-delta,q-delta,by dsimp [delta]; linarith,
      by change p-delta < p; dsimp [delta]; linarith,
      by change q-delta < q; dsimp [delta]; linarith⟩
  · rintro r ⟨a,b,h,ha,hb⟩
    change a < p at ha; change b < q at hb
    change r < p+q; linarith

theorem req_trans (x y z : R) (hxy : Req x y) (hyz : Req y z) : Req x z :=
  ⟨fun q h => hyz.1 q (hxy.1 q h),fun q h => hxy.2 q (hyz.2 q h)⟩

theorem spec_Rplus_0_r : _root_.spec_Rplus_0_r canonical := by
  intro x
  exact req_trans _ _ _ (spec_Rplus_comm x (R_of_Q 0)) (spec_Rplus_0_l x)

theorem spec_Rplus_assoc : _root_.spec_Rplus_assoc canonical := by
  intro x y z
  constructor
  · rintro q ⟨r,c,h,⟨a,b,hab,ha,hb⟩,hc⟩
    let s := (q-a+b+c)/2
    exact ⟨a,s,by dsimp [s]; linarith,ha,b,c,by dsimp [s]; linarith,hb,hc⟩
  · rintro q ⟨a,r,h,ha,⟨b,c,hbc,hb,hc⟩⟩
    let s := (q-c+a+b)/2
    exact ⟨s,c,by dsimp [s]; linarith,⟨a,b,by dsimp [s]; linarith,ha,hb⟩,hc⟩

theorem spec_Rplus_opp_r : _root_.spec_Rplus_opp_r canonical := by
  intro x
  change Req (Rplus x (Ropp x)) (R_of_Q 0)
  constructor
  · rintro q ⟨a,b,h,ha,hb⟩
    have := lower_upper x ha hb
    change q < 0; linarith
  · intro q hq
    change q < 0 at hq
    obtain ⟨a,b,ha,hb,hab⟩ := straddle x (-q/2) (by linarith)
    exact ⟨a,-b,by linarith,ha,by simpa [Ropp] using hb⟩

theorem spec_Rplus_opp_l : _root_.spec_Rplus_opp_l canonical := by
  intro x
  exact req_trans _ _ _ (spec_Rplus_comm (Ropp x) x) (spec_Rplus_opp_r x)

theorem spec_Ropp_plus_distr : _root_.spec_Ropp_plus_distr canonical := by
  intro x y
  change Req (Ropp (Rplus x y)) (Rplus (Ropp x) (Ropp y))
  constructor
  · rintro q ⟨a,b,h,ha,hb⟩
    exact ⟨-a,-b,by linarith,by simpa [Ropp] using ha,by simpa [Ropp] using hb⟩
  · rintro q ⟨a,b,h,ha,hb⟩
    exact ⟨-a,-b,by linarith,ha,hb⟩

theorem spec_Rplus_positive : _root_.spec_Rplus_positive canonical := by
  rintro x y ⟨q,hq,⟨a,b,h,ha,hb⟩⟩
  change 0 < q at hq
  by_cases hapos : 0 < a
  · exact Or.inl ⟨a,hapos,ha⟩
  · exact Or.inr ⟨b,by change 0 < b; linarith,hb⟩

theorem spec_Ropp_min : _root_.spec_Ropp_min canonical := by
  intro x y
  constructor <;> intro q h <;> exact h
theorem spec_Ropp_max : _root_.spec_Ropp_max canonical := by
  intro x y
  constructor <;> intro q h <;> exact h

theorem spec_dedekind_complete : _root_.spec_dedekind_complete canonical := by
  intro c
  constructor
  · intro x
    constructor
    · intro hx
      obtain ⟨y,hxy,hy⟩ := c.r_lower_open x hx
      obtain ⟨q,hxq,hyq⟩ := hxy
      exact ⟨q,hxq,y,hy,hyq⟩
    · rintro ⟨q,hxq,⟨y,hy,hyq⟩⟩
      exact c.r_lower_lower x y ⟨q,hxq,hyq⟩ hy
  · intro x
    constructor
    · intro hx
      obtain ⟨y,hyx,hy⟩ := c.r_upper_open x hx
      obtain ⟨q,hyq,hxq⟩ := hyx
      exact ⟨q,⟨y,hy,hyq⟩,hxq⟩
    · rintro ⟨q,⟨y,hy,hyq⟩,hxq⟩
      exact c.r_upper_upper y x ⟨q,hyq,hxq⟩ hy

theorem rat_abs_eq (q : Rat) : Rat.abs q = |q| := by
  unfold Rat.abs
  split <;> simp_all [abs_of_nonneg,abs_of_neg,le_of_not_gt]

theorem series_difference_bound (un vn : Nat → Rat)
    (h : ∀ n, Rat.abs (un n) ≤ vn n) (n p : Nat) (hnp : n ≤ p) :
    |sum_f_Q0 un p-sum_f_Q0 un n| ≤ sum_f_Q0 vn p-sum_f_Q0 vn n := by
  induction p, hnp using Nat.le_induction with
  | base => simp
  | succ p hnp ih =>
    have h' : |un (p+1)| ≤ vn (p+1) := by
      have := h (p+1)
      simpa only [rat_abs_eq] using this
    calc
      |sum_f_Q0 un (p+1)-sum_f_Q0 un n| = |(sum_f_Q0 un p-sum_f_Q0 un n)+un (p+1)| := by
        congr 1; simp only [sum_f_Q0]; ring
      _ ≤ |sum_f_Q0 un p-sum_f_Q0 un n|+|un (p+1)| := abs_add_le _ _
      _ ≤ (sum_f_Q0 vn p-sum_f_Q0 vn n)+vn (p+1) := add_le_add ih h'
      _ = sum_f_Q0 vn (p+1)-sum_f_Q0 vn n := by simp only [sum_f_Q0]; ring

theorem spec_Cauchy_series_maj : _root_.spec_Cauchy_series_maj canonical := by
  intro un vn h hc eps heps
  obtain ⟨n,hn⟩ := hc eps heps
  refine ⟨n,?_⟩
  intro i j hi hj
  have hv := hn j i hj hi
  have hv' := hn i j hi hj
  rw [rat_abs_eq] at hv hv' ⊢
  rcases le_total i j with hij | hji
  · have hb := series_difference_bound un vn h i j hij
    have hb0 : 0 ≤ sum_f_Q0 vn j-sum_f_Q0 vn i := le_trans (abs_nonneg _) hb
    rw [abs_of_nonneg hb0] at hv
    rw [abs_sub_comm]
    exact lt_of_le_of_lt hb hv
  · have hb := series_difference_bound un vn h j i hji
    have hb0 : 0 ≤ sum_f_Q0 vn i-sum_f_Q0 vn j := le_trans (abs_nonneg _) hb
    rw [abs_of_nonneg hb0] at hv'
    exact lt_of_le_of_lt hb hv'

theorem spec_Rmin_plus_distr_r : _root_.spec_Rmin_plus_distr_r canonical := by
  intro x y z
  constructor
  · rintro q ⟨⟨a,b,h,ha,hb⟩,⟨c,d,h',hc,hd⟩⟩
    refine ⟨min a c,max b d,?_,⟨lower_le x (min_le_left _ _) ha,lower_le y (min_le_right _ _) hc⟩,?_⟩
    · rcases le_total a c with hac | hca
      · rw [min_eq_left hac]; have := le_max_left b d; linarith
      · rw [min_eq_right hca]; have := le_max_right b d; linarith
    · rcases le_total b d with hbd | hdb
      · simpa only [max_eq_right hbd] using hd
      · simpa only [max_eq_left hdb] using hb
  · rintro q ⟨a,b,h,⟨ha,ha'⟩,hb⟩
    exact ⟨⟨a,b,h,ha,hb⟩,⟨a,b,h,ha',hb⟩⟩

theorem spec_Rmin_plus_distr_l : _root_.spec_Rmin_plus_distr_l canonical := by
  intro x y z
  constructor
  · rintro q ⟨⟨a,b,h,ha,hb⟩,⟨c,d,h',hc,hd⟩⟩
    refine ⟨max a c,min b d,?_,?_,⟨lower_le y (min_le_left _ _) hb,lower_le z (min_le_right _ _) hd⟩⟩
    · rcases le_total b d with hbd | hdb
      · rw [min_eq_left hbd]; have := le_max_left a c; linarith
      · rw [min_eq_right hdb]; have := le_max_right a c; linarith
    · rcases le_total a c with hac | hca
      · simpa only [max_eq_right hac] using hc
      · simpa only [max_eq_left hca] using ha
  · rintro q ⟨a,b,h,ha,⟨hb,hb'⟩⟩
    exact ⟨⟨a,b,h,ha,hb⟩,⟨a,b,h,ha,hb'⟩⟩

theorem spec_Rmax_plus_distr_r : _root_.spec_Rmax_plus_distr_r canonical := by
  intro x y z
  constructor
  · rintro q (⟨a,b,h,ha,hb⟩ | ⟨a,b,h,ha,hb⟩)
    · exact ⟨a,b,h,Or.inl ha,hb⟩
    · exact ⟨a,b,h,Or.inr ha,hb⟩
  · rintro q ⟨a,b,h,ha,hb⟩
    exact ha.elim (fun ha => Or.inl ⟨a,b,h,ha,hb⟩) (fun ha => Or.inr ⟨a,b,h,ha,hb⟩)

theorem spec_Rmax_plus_distr_l : _root_.spec_Rmax_plus_distr_l canonical := by
  intro x y z
  constructor
  · rintro q (⟨a,b,h,ha,hb⟩ | ⟨a,b,h,ha,hb⟩)
    · exact ⟨a,b,h,ha,Or.inl hb⟩
    · exact ⟨a,b,h,ha,Or.inr hb⟩
  · rintro q ⟨a,b,h,ha,hb⟩
    exact hb.elim (fun hb => Or.inl ⟨a,b,h,ha,hb⟩) (fun hb => Or.inr ⟨a,b,h,ha,hb⟩)

end DedekindCertificates
