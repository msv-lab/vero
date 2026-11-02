import Flocq.Bundle

set_option maxRecDepth 4000
set_option maxHeartbeats 30000
set_option linter.unusedSimpArgs false
namespace FlocqCertificates

theorem spec_newLocationEven_lo :
    ∀ (nb_steps k : Int) (l : Location),
    k ≠ 0 → 2 * k < nb_steps →
    Flocq.newLocationEven nb_steps k l = Location.Inexact Ordering.lt := by
  intro nb k l hk h
  have hc := Int.compare_eq_lt.mpr h
  dsimp only [Flocq.newLocationEven]
  simp [hk, hc]

theorem spec_newLocationEven_hi :
    ∀ (nb_steps k : Int) (l : Location),
    k ≠ 0 → 2 * k > nb_steps →
    Flocq.newLocationEven nb_steps k l = Location.Inexact Ordering.gt := by
  intro nb k l hk h
  have hc := Int.compare_eq_gt.mpr h
  dsimp only [Flocq.newLocationEven]
  simp [hk, hc]

theorem spec_newLocationOdd_lo :
    ∀ (nb_steps k : Int) (l : Location),
    k ≠ 0 → 2 * k + 1 < nb_steps →
    Flocq.newLocationOdd nb_steps k l = Location.Inexact Ordering.lt := by
  intro nb k l hk h
  have hc := Int.compare_eq_lt.mpr h
  dsimp only [Flocq.newLocationOdd]
  simp [hk, hc]

theorem spec_newLocationOdd_hi :
    ∀ (nb_steps k : Int) (l : Location),
    k ≠ 0 → 2 * k + 1 > nb_steps →
    Flocq.newLocationOdd nb_steps k l = Location.Inexact Ordering.gt := by
  intro nb k l hk h
  have hc := Int.compare_eq_gt.mpr h
  dsimp only [Flocq.newLocationOdd]
  simp [hk, hc]

theorem spec_fdivCore_quotient_hi :
    ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    ¬(e ≤ e1 - e2) →
    (Flocq.fdivCore beta fexp m1 e1 m2 e2 e).1 =
      m1 / (m2 * beta.val ^ (e - (e1 - e2)).toNat) := by
  intros
  dsimp only [Flocq.fdivCore, Flocq.newLocation, Flocq.newLocationEven, Flocq.newLocationOdd] at *
  try simp_all only [pow_zero, pow_succ]
  try split_ifs
  all_goals try simp_all
  all_goals first | rfl | omega | linarith | left; rfl

theorem spec_fdivCore_exact_lo :
    ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    e ≤ e1 - e2 →
    (m1 * beta.val ^ (e1 - e2 - e).toNat) % m2 = 0 →
    (Flocq.fdivCore beta fexp m1 e1 m2 e2 e).2 = Location.Exact := by
  intros
  dsimp only [Flocq.fdivCore, Flocq.newLocation, Flocq.newLocationEven, Flocq.newLocationOdd] at *
  try simp_all only [pow_zero, pow_succ]
  try split_ifs
  all_goals try simp_all
  all_goals first | rfl | omega | linarith | left; rfl

theorem spec_fdivCore_exact_hi :
    ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    ¬(e ≤ e1 - e2) →
    m1 % (m2 * beta.val ^ (e - (e1 - e2)).toNat) = 0 →
    (Flocq.fdivCore beta fexp m1 e1 m2 e2 e).2 = Location.Exact := by
  intros
  dsimp only [Flocq.fdivCore, Flocq.newLocation, Flocq.newLocationEven, Flocq.newLocationOdd] at *
  try simp_all only [pow_zero, pow_succ]
  try split_ifs
  all_goals try simp_all
  all_goals first | rfl | omega | linarith | left; rfl

theorem spec_falign_exp_gt :
    ∀ (β : Radix) (f1 f2 : FloatNum),
    ¬ f1.Fexp ≤ f2.Fexp →
    (Flocq.falign β f1 f2).2 = f2.Fexp := by
  intros
  dsimp only [Flocq.falign] at *
  try simp_all only [pow_zero, pow_succ]
  try split_ifs
  all_goals try simp_all
  all_goals first | rfl | omega | linarith | left; rfl

theorem spec_falign_right_mantissa_le :
    ∀ (β : Radix) (f1 f2 : FloatNum),
    f1.Fexp ≤ f2.Fexp →
    (Flocq.falign β f1 f2).1.2 =
      f2.Fnum * β.val ^ (f2.Fexp - f1.Fexp).natAbs := by
  intros
  dsimp only [Flocq.falign] at *
  try simp_all only [pow_zero, pow_succ]
  try split_ifs
  all_goals try simp_all
  all_goals first | rfl | omega | linarith | left; rfl

theorem spec_fplusCore_mantissa_lo :
    ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    e ≤ e2 →
    (Flocq.fplusCore beta fexp m1 e1 m2 e2 e).1 =
      m1 * beta.val ^ (e1 - e).toNat + m2 * beta.val ^ (e2 - e).toNat := by
  intros
  dsimp only [Flocq.fplusCore, Flocq.truncateAux, Flocq.newLocation, Flocq.newLocationEven, Flocq.newLocationOdd] at *
  try simp_all only [pow_zero, pow_succ]
  try split_ifs
  all_goals try simp_all
  all_goals first | rfl | omega | linarith | left; rfl

theorem spec_fplusCore_location_exact_lo :
    ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    e ≤ e2 →
    (Flocq.fplusCore beta fexp m1 e1 m2 e2 e).2 = Location.Exact := by
  intros
  dsimp only [Flocq.fplusCore, Flocq.truncateAux, Flocq.newLocation, Flocq.newLocationEven, Flocq.newLocationOdd] at *
  try simp_all only [pow_zero, pow_succ]
  try split_ifs
  all_goals try simp_all
  all_goals first | rfl | omega | linarith | left; rfl

theorem spec_Rle_bool_spec :
    ∀ (x y : ℝ), Flocq.rleBool x y = true ↔ x ≤ y := by
  intros
  dsimp only [Flocq.rleBool, Rcompare, RleBool, RltBool, ReqBool] at *
  try simp_all only [pow_zero, pow_succ]
  try split_ifs
  all_goals try simp_all
  all_goals first | rfl | omega | linarith | left; rfl

theorem spec_Rlt_bool_spec :
    ∀ (x y : ℝ), Flocq.rltBool x y = true ↔ x < y := by
  intros
  dsimp only [Flocq.rltBool, Rcompare, RleBool, RltBool, ReqBool] at *
  try simp_all only [pow_zero, pow_succ]
  try split_ifs
  all_goals try simp_all
  all_goals first | rfl | omega | linarith | left; rfl

theorem spec_Req_bool_spec :
    ∀ (x y : ℝ), Flocq.reqBool x y = true ↔ x = y := by
  intros
  dsimp only [Flocq.reqBool, Rcompare, RleBool, RltBool, ReqBool] at *
  try simp_all only [pow_zero, pow_succ]
  try split_ifs
  all_goals try simp_all
  all_goals first | rfl | omega | linarith | left; rfl

theorem spec_zfastPowPos_zero :
    ∀ (v : Int), Flocq.zfastPowPos v 0 = 1 := by
  intros
  dsimp only [Flocq.zfastPowPos, zpowerPos] at *
  try simp_all only [pow_zero, pow_succ]
  try split_ifs
  all_goals try simp_all
  all_goals first | rfl | omega | linarith | left; rfl

theorem spec_zfastPowPos_succ :
    ∀ (v : Int) (n : Nat),
    Flocq.zfastPowPos v (n + 1) = Flocq.zfastPowPos v n * v := by
  intros
  dsimp only [Flocq.zfastPowPos, zpowerPos] at *
  try simp_all only [pow_zero, pow_succ]
  try split_ifs
  all_goals try simp_all
  all_goals first | rfl | omega | linarith | left; rfl

theorem spec_pffMProd_mem :
    ∀ (A B : Type) (xs : List A) (ys : List B) (x : A) (y : B),
    x ∈ xs → y ∈ ys → (x, y) ∈ Flocq.pffMProd A B xs ys := by
  intro A B xs ys x y hx hy
  induction xs with
  | nil => simp at hx
  | cons a rest ih =>
    simp only [List.mem_cons] at hx
    simp only [Flocq.pffMProd, Flocq.pffMProd.go, List.mem_append, List.mem_map]
    rcases hx with rfl | hx
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr (ih hx)

theorem spec_fdiv_delegation :
    ∀ (beta : Radix) (fexp : Int → Int) (x y : FloatNum),
    let e' := (Flocq.zdigits beta x.Fnum + x.Fexp) -
              (Flocq.zdigits beta y.Fnum + y.Fexp)
    let e := min (min (fexp e') (fexp (e' + 1))) (x.Fexp - y.Fexp)
    let core := Flocq.fdivCore beta fexp x.Fnum x.Fexp y.Fnum y.Fexp e
    (Flocq.fdiv beta fexp x y).1 = core.1 ∧
    (Flocq.fdiv beta fexp x y).2.2 = core.2 := by
  intros
  constructor <;> rfl

theorem spec_fsqrt_delegation :
    ∀ (beta : Radix) (fexp : Int → Int) (x : FloatNum),
    let e' := Flocq.zdigits beta x.Fnum + x.Fexp + 1
    let e := min (fexp (Flocq.zdiv2 e')) (Flocq.zdiv2 x.Fexp)
    let core := Flocq.fsqrtCore beta x.Fnum x.Fexp e
    (Flocq.fsqrt beta fexp x).1 = core.1 ∧
    (Flocq.fsqrt beta fexp x).2.2 = core.2 := by
  intros
  constructor <;> rfl

theorem spec_Rcompare_spec :
    ∀ (x y : ℝ),
    match Flocq.rcompare x y with
    | Ordering.lt => x < y
    | Ordering.eq => x = y
    | Ordering.gt => y < x := by
  intro x y
  dsimp only [Flocq.rcompare, Rcompare]
  split_ifs with hlt heq
  · exact hlt
  · exact heq
  · exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)

theorem spec_b2R_def :
    (∀ (prec emax : Int) (s : Bool),
    Flocq.b2R prec emax (BinaryFloat.zero s) = 0) ∧
  (∀ (prec emax : Int) (s : Bool),
    Flocq.b2R prec emax (BinaryFloat.inf s) = 0) ∧
  (∀ (prec emax : Int) (s : Bool) (payload : Nat),
    Flocq.b2R prec emax (BinaryFloat.nan s payload) = 0) ∧
  (∀ (prec emax : Int) (s : Bool) (m : Nat) (e : Int),
    Flocq.b2R prec emax (BinaryFloat.finite s m e) =
      (if s then -1 else 1 : ℝ) * (m : ℝ) * Flocq.bpow radix2 e) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

theorem spec_isFinite_def :
    (∀ (prec emax : Int) (s : Bool),
    Flocq.isFinite prec emax (BinaryFloat.zero s) = true) ∧
  (∀ (prec emax : Int) (s : Bool),
    Flocq.isFinite prec emax (BinaryFloat.inf s) = false) ∧
  (∀ (prec emax : Int) (s : Bool) (payload : Nat),
    Flocq.isFinite prec emax (BinaryFloat.nan s payload) = false) ∧
  (∀ (prec emax : Int) (s : Bool) (m : Nat) (e : Int),
    Flocq.isFinite prec emax (BinaryFloat.finite s m e) = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

theorem spec_isNaN_def :
    (∀ (prec emax : Int) (s : Bool),
    Flocq.isNaN prec emax (BinaryFloat.zero s) = false) ∧
  (∀ (prec emax : Int) (s : Bool),
    Flocq.isNaN prec emax (BinaryFloat.inf s) = false) ∧
  (∀ (prec emax : Int) (s : Bool) (payload : Nat),
    Flocq.isNaN prec emax (BinaryFloat.nan s payload) = true) ∧
  (∀ (prec emax : Int) (s : Bool) (m : Nat) (e : Int),
    Flocq.isNaN prec emax (BinaryFloat.finite s m e) = false) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

theorem spec_roundMode_def :
    (∀ (x : ℝ), Flocq.roundMode RoundingMode.DN x = Zfloor x) ∧
  (∀ (x : ℝ), Flocq.roundMode RoundingMode.UP x = Zceil x) ∧
  (∀ (x : ℝ), Flocq.roundMode RoundingMode.ZR x = Ztrunc x) ∧
  (∀ (x : ℝ), Flocq.roundMode RoundingMode.NE x = Znearest (fun _ => false) x) ∧
  (∀ (x : ℝ), Flocq.roundMode RoundingMode.NA x = Znearest (fun _ => true) x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rfl

theorem spec_pffMZlist_mem :
    ∀ lo hi r : Int,
    lo <= r → r <= hi → r ∈ Flocq.pffMZlist lo hi := by
  intro lo hi r hlo hhi
  have h : lo ≤ hi := by omega
  have hr : 0 ≤ r - lo := by omega
  have hcast : ((r - lo).toNat : Int) = r - lo := Int.toNat_of_nonneg hr
  simp only [Flocq.pffMZlist, h, ↓reduceIte, Flocq.pffMZlistAux, List.mem_map, List.mem_range]
  refine ⟨(r - lo).toNat, ?_, ?_⟩
  · exact Nat.lt_succ_of_le (Int.toNat_le_toNat (by omega))
  · change lo + ((r - lo).toNat : Int) = r
    rw [hcast]
    omega

end FlocqCertificates
