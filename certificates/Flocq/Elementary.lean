import Flocq.Bundle

set_option maxRecDepth 4000
set_option maxHeartbeats 30000
set_option linter.unusedSimpArgs false
namespace FlocqCertificates

theorem spec_newLocationEven_k0_exact :
    ∀ (nb_steps : Int),
    Flocq.newLocationEven nb_steps 0 Location.Exact = Location.Exact := by
  intros
  rfl

theorem spec_newLocationEven_k0_inexact :
    ∀ (nb_steps : Int) (o : Ordering),
    Flocq.newLocationEven nb_steps 0 (Location.Inexact o) =
      Location.Inexact Ordering.lt := by
  intros
  rfl

theorem spec_newLocationOdd_k0_exact :
    ∀ (nb_steps : Int),
    Flocq.newLocationOdd nb_steps 0 Location.Exact = Location.Exact := by
  intros
  rfl

theorem spec_newLocationOdd_k0_inexact :
    ∀ (nb_steps : Int) (o : Ordering),
    Flocq.newLocationOdd nb_steps 0 (Location.Inexact o) =
      Location.Inexact Ordering.lt := by
  intros
  rfl

theorem spec_fdiv_exponent :
    ∀ (beta : Radix) (fexp : Int → Int) (x y : FloatNum),
    let e' := (Flocq.zdigits beta x.Fnum + x.Fexp) -
              (Flocq.zdigits beta y.Fnum + y.Fexp)
    (Flocq.fdiv beta fexp x y).2.1 =
      min (min (fexp e') (fexp (e' + 1))) (x.Fexp - y.Fexp) := by
  intros
  rfl

theorem spec_fopp_num :
    ∀ (f : FloatNum), (Flocq.fopp f).Fnum = -f.Fnum := by
  intros
  rfl

theorem spec_fopp_exp :
    ∀ (f : FloatNum), (Flocq.fopp f).Fexp = f.Fexp := by
  intros
  rfl

theorem spec_fabs_num :
    ∀ (f : FloatNum), (Flocq.fabs f).Fnum = Int.ofNat f.Fnum.natAbs := by
  intros
  rfl

theorem spec_fabs_exp :
    ∀ (f : FloatNum), (Flocq.fabs f).Fexp = f.Fexp := by
  intros
  rfl

theorem spec_fmult_mantissa :
    ∀ (f1 f2 : FloatNum),
    (Flocq.fmult f1 f2).Fnum = f1.Fnum * f2.Fnum := by
  intros
  rfl

theorem spec_fmult_exponent :
    ∀ (f1 f2 : FloatNum),
    (Flocq.fmult f1 f2).Fexp = f1.Fexp + f2.Fexp := by
  intros
  rfl

theorem spec_condIncr_true :
    ∀ (m : Int), Flocq.condIncr true m = m + 1 := by
  intros
  rfl

theorem spec_condIncr_false :
    ∀ (m : Int), Flocq.condIncr false m = m := by
  intros
  rfl

theorem spec_roundSignDN_exact :
    ∀ (s : Bool), Flocq.roundSignDN s Location.Exact = false := by
  intros
  rfl

theorem spec_roundSignDN_inexact :
    ∀ (s : Bool) (o : Ordering), Flocq.roundSignDN s (Location.Inexact o) = s := by
  intros
  rfl

theorem spec_roundUP_exact :
    Flocq.roundUP Location.Exact = false := by
  intros
  rfl

theorem spec_roundUP_inexact :
    ∀ (o : Ordering), Flocq.roundUP (Location.Inexact o) = true := by
  intros
  rfl

theorem spec_roundSignUP_inexact :
    ∀ (s : Bool) (o : Ordering), Flocq.roundSignUP s (Location.Inexact o) = !s := by
  intros
  rfl

theorem spec_roundZR_inexact :
    ∀ (s : Bool) (o : Ordering), Flocq.roundZR s (Location.Inexact o) = s := by
  intros
  rfl

theorem spec_roundN_lt :
    ∀ (p : Bool), Flocq.roundN p (Location.Inexact Ordering.lt) = false := by
  intros
  rfl

theorem spec_roundN_eq :
    ∀ (p : Bool), Flocq.roundN p (Location.Inexact Ordering.eq) = p := by
  intros
  rfl

theorem spec_roundN_gt :
    ∀ (p : Bool), Flocq.roundN p (Location.Inexact Ordering.gt) = true := by
  intros
  rfl

theorem spec_truncateAux_mantissa :
    ∀ (β : Radix) (m e k : Int) (l : Location),
    (Flocq.truncateAux β (m, e, l) k).1 = m / β.val ^ k.natAbs := by
  intros
  rfl

theorem spec_truncateAux_exponent :
    ∀ (β : Radix) (m e k : Int) (l : Location),
    (Flocq.truncateAux β (m, e, l) k).2.1 = e + k := by
  intros
  rfl

theorem spec_truncateAux_location :
    ∀ (β : Radix) (m e k : Int) (l : Location),
    (Flocq.truncateAux β (m, e, l) k).2.2 =
      Flocq.newLocation (β.val ^ k.natAbs) (m % (β.val ^ k.natAbs)) l := by
  intros
  rfl

theorem spec_fsqrt_exponent :
    ∀ (beta : Radix) (fexp : Int → Int) (x : FloatNum),
    let e' := Flocq.zdigits beta x.Fnum + x.Fexp + 1
    (Flocq.fsqrt beta fexp x).2.1 =
      min (fexp (Flocq.zdiv2 e')) (Flocq.zdiv2 x.Fexp) := by
  intros
  rfl

theorem spec_digits2Pnat_zero :
    Flocq.digits2Pnat 0 = 0 := by
  intros
  rfl

theorem spec_zsumDigit_def :
    ∀ (digit k : Int), Flocq.zsumDigit digit k = digit * k := by
  intros
  rfl

theorem spec_zdigitsAux_def :
    ∀ (absN beta nb pow : Int) (fuel : Nat),
    Flocq.zdigitsAux absN beta nb pow fuel = zdigitsAuxCore absN beta nb pow fuel := by
  intros
  rfl

theorem spec_zdigits_zero :
    ∀ (r : Radix), Flocq.zdigits r 0 = 0 := by
  intros
  rfl

theorem spec_znearest_def :
    ∀ (choice : Int → Bool) (x : ℝ),
    Flocq.znearest choice x = Znearest choice x := by
  intros
  rfl

theorem spec_rcompare_def :
    ∀ (x y : ℝ), Flocq.rcompare x y = Rcompare x y := by
  intros
  rfl

theorem spec_rleBool_def :
    ∀ (x y : ℝ), Flocq.rleBool x y = (if x ≤ y then true else false) := by
  intros
  rfl

theorem spec_rltBool_def :
    ∀ (x y : ℝ), Flocq.rltBool x y = (if x < y then true else false) := by
  intros
  rfl

theorem spec_reqBool_def :
    ∀ (x y : ℝ), Flocq.reqBool x y = (if x = y then true else false) := by
  intros
  rfl

theorem spec_ztrunc_def :
    ∀ (x : ℝ), Flocq.ztrunc x = Ztrunc x := by
  intros
  rfl

theorem spec_zaway_def :
    ∀ (x : ℝ), Flocq.zaway x = Zaway x := by
  intros
  rfl

theorem spec_condRopp_true :
    ∀ (x : ℝ), Flocq.condRopp true x = -x := by
  intros
  rfl

theorem spec_condRopp_false :
    ∀ (x : ℝ), Flocq.condRopp false x = x := by
  intros
  rfl

theorem spec_Zfast_pow_pos_correct :
    ∀ (v : Int) (n : Nat), Flocq.zfastPowPos v n = v ^ n := by
  intros
  rfl

theorem spec_zposDivEuclAux1_quot :
    ∀ (a b : Int), (Flocq.zposDivEuclAux1 a b).1 = Int.ediv a b := by
  intros
  rfl

theorem spec_zposDivEuclAux1_rem :
    ∀ (a b : Int), (Flocq.zposDivEuclAux1 a b).2 = Int.emod a b := by
  intros
  rfl

theorem spec_zfastDivEucl_quot :
    ∀ (a b : Int), (Flocq.zfastDivEucl a b).1 = Int.ediv a b := by
  intros
  rfl

theorem spec_zfastDivEucl_rem :
    ∀ (a b : Int), (Flocq.zfastDivEucl a b).2 = Int.emod a b := by
  intros
  rfl

theorem spec_Zfast_div_eucl_correct :
    ∀ (a b : Int), Flocq.zfastDivEucl a b = (Int.ediv a b, Int.emod a b) := by
  intros
  rfl

theorem spec_iterNat_zero :
    ∀ {α : Type} (f : α → α) (x : α), Flocq.iterNat f 0 x = x := by
  intros
  rfl

theorem spec_iterNat_succ :
    ∀ {α : Type} (f : α → α) (n : Nat) (x : α),
    Flocq.iterNat f (n + 1) x = Flocq.iterNat f n (f x) := by
  intros
  rfl

theorem spec_b2FF_identity :
    ∀ (prec emax : Int) (x : BinaryFloat prec emax),
    Flocq.b2FF prec emax x = x := by
  intros
  rfl

theorem spec_ff2B_identity :
    ∀ (prec emax : Int) (x : BinaryFloat prec emax),
    Flocq.ff2B prec emax x = x := by
  intros
  rfl

theorem spec_binaryNormalize_def :
    ∀ (prec emax : Int) (mode : RoundingMode) (m e : Int) (szero : Bool),
    Flocq.binaryNormalize prec emax mode m e szero =
      Flocq.binaryNormalize prec emax mode m e szero := by
  intros
  rfl

theorem spec_babs_nan :
    ∀ (prec emax : Int)
    (nanH : BinaryFloat prec emax → BinaryFloat prec emax)
    (s : Bool) (payload : Nat),
    Flocq.babs prec emax nanH (BinaryFloat.nan s payload) =
      nanH (BinaryFloat.nan s payload) := by
  intros
  rfl

theorem spec_babs_finite :
    ∀ (prec emax : Int)
    (nanH : BinaryFloat prec emax → BinaryFloat prec emax)
    (s : Bool) (m : Nat) (e : Int),
    Flocq.babs prec emax nanH (BinaryFloat.finite s m e) =
      BinaryFloat.finite false m e := by
  intros
  rfl

theorem spec_babs_zero :
    ∀ (prec emax : Int)
    (nanH : BinaryFloat prec emax → BinaryFloat prec emax)
    (s : Bool),
    Flocq.babs prec emax nanH (BinaryFloat.zero s) = BinaryFloat.zero false := by
  intros
  rfl

theorem spec_bmaxFloat_def :
    ∀ (prec emax : Int) (s : Bool),
    Flocq.bmaxFloat prec emax s =
      BinaryFloat.finite s ((2 : Nat) ^ prec.toNat - 1) (emax - prec) := by
  intros
  rfl

theorem spec_bopp_nan :
    ∀ (prec emax : Int)
    (nanH : BinaryFloat prec emax → BinaryFloat prec emax)
    (s : Bool) (payload : Nat),
    Flocq.bopp prec emax nanH (BinaryFloat.nan s payload) =
      nanH (BinaryFloat.nan s payload) := by
  intros
  rfl

theorem spec_bopp_finite :
    ∀ (prec emax : Int)
    (nanH : BinaryFloat prec emax → BinaryFloat prec emax)
    (s : Bool) (m : Nat) (e : Int),
    Flocq.bopp prec emax nanH (BinaryFloat.finite s m e) =
      BinaryFloat.finite (!s) m e := by
  intros
  rfl

theorem spec_bopp_zero :
    ∀ (prec emax : Int)
    (nanH : BinaryFloat prec emax → BinaryFloat prec emax)
    (s : Bool),
    Flocq.bopp prec emax nanH (BinaryFloat.zero s) = BinaryFloat.zero (!s) := by
  intros
  rfl

theorem spec_binopNanPl32_def :
    ∀ (x y : Binary32),
    Flocq.binopNanPl32 x y = BinaryFloat.nan false 1 := by
  intros
  rfl

theorem spec_binopNanPl64_def :
    ∀ (x y : Binary64),
    Flocq.binopNanPl64 x y = BinaryFloat.nan false 1 := by
  intros
  rfl

theorem spec_unopNanPl32_def :
    ∀ (x : Binary32),
    Flocq.unopNanPl32 x = BinaryFloat.nan false 1 := by
  intros
  rfl

theorem spec_unopNanPl64_def :
    ∀ (x : Binary64),
    Flocq.unopNanPl64 x = BinaryFloat.nan false 1 := by
  intros
  rfl

theorem spec_ternopNanPl32_def :
    ∀ (x y z : Binary32),
    Flocq.ternopNanPl32 x y z = BinaryFloat.nan false 1 := by
  intros
  rfl

theorem spec_ternopNanPl64_def :
    ∀ (x y z : Binary64),
    Flocq.ternopNanPl64 x y z = BinaryFloat.nan false 1 := by
  intros
  rfl

theorem spec_splitBits_fields :
    ∀ (mw ew : Nat) (n : Int),
    let mm := (2 : Int) ^ mw
    let em := (2 : Int) ^ ew
    Flocq.splitBits mw ew n =
      (decide (mm * em ≤ n), (n / mm) % em, n % mm) := by
  intros
  rfl

theorem spec_split_bits_of_binary_float_correct :
    ∀ (mw ew : Int) (x : BinaryFloat (mw + 1) ((2 : Int) ^ (ew - 1).toNat)),
    Flocq.splitBits mw.toNat ew.toNat (Flocq.bitsOfBinaryFloat mw ew x) =
      Flocq.splitBitsOfBinaryFloat mw ew x := by
  intros
  rfl

theorem spec_bitsOfB32_def :
    ∀ (x : Binary32), Flocq.bitsOfB32 x = Flocq.bitsOfBinaryFloat 23 8 x := by
  intros
  rfl

theorem spec_bitsOfB64_def :
    ∀ (x : Binary64), Flocq.bitsOfB64 x = Flocq.bitsOfBinaryFloat 52 11 x := by
  intros
  rfl

theorem spec_pffFopp_num :
    ∀ x : PffFloat, (Flocq.pffFopp x).num = -x.num := by
  intros
  rfl

theorem spec_pffFopp_exp :
    ∀ x : PffFloat, (Flocq.pffFopp x).exp = x.exp := by
  intros
  rfl

theorem spec_pffFabs_num :
    ∀ x : PffFloat, (Flocq.pffFabs x).num = pffAbs x.num := by
  intros
  rfl

theorem spec_pffFabs_exp :
    ∀ x : PffFloat, (Flocq.pffFabs x).exp = x.exp := by
  intros
  rfl

theorem spec_pffFmult_num :
    ∀ x y : PffFloat, (Flocq.pffFmult x y).num = x.num * y.num := by
  intros
  rfl

theorem spec_pffFmult_exp :
    ∀ x y : PffFloat, (Flocq.pffFmult x y).exp = x.exp + y.exp := by
  intros
  rfl

end FlocqCertificates
