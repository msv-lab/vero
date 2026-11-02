import Flocq.Bundle

set_option maxRecDepth 4000
set_option maxHeartbeats 30000
set_option linter.unusedSimpArgs false
namespace FlocqCertificates

theorem spec_newLocationEven_mid_exact :
    ∀ (nb_steps k : Int),
    k ≠ 0 → 2 * k = nb_steps →
    Flocq.newLocationEven nb_steps k Location.Exact =
      Location.Inexact Ordering.eq := by
  intros
  dsimp only [Flocq.newLocationEven] at *
  simp_all

theorem spec_newLocationEven_mid_inexact :
    ∀ (nb_steps k : Int) (o : Ordering),
    k ≠ 0 → 2 * k = nb_steps →
    Flocq.newLocationEven nb_steps k (Location.Inexact o) =
      Location.Inexact Ordering.gt := by
  intros
  dsimp only [Flocq.newLocationEven] at *
  simp_all

theorem spec_newLocationOdd_mid_exact :
    ∀ (nb_steps k : Int),
    k ≠ 0 → 2 * k + 1 = nb_steps →
    Flocq.newLocationOdd nb_steps k Location.Exact =
      Location.Inexact Ordering.lt := by
  intros
  dsimp only [Flocq.newLocationOdd] at *
  simp_all

theorem spec_newLocationOdd_mid_inexact :
    ∀ (nb_steps k : Int) (o : Ordering),
    k ≠ 0 → 2 * k + 1 = nb_steps →
    Flocq.newLocationOdd nb_steps k (Location.Inexact o) =
      Location.Inexact o := by
  intros
  dsimp only [Flocq.newLocationOdd] at *
  simp_all

theorem spec_newLocation_even :
    ∀ (nb_steps k : Int) (l : Location),
    nb_steps % 2 = 0 →
    Flocq.newLocation nb_steps k l =
      Flocq.newLocationEven nb_steps k l := by
  intros
  dsimp only [Flocq.newLocation, Flocq.newLocationEven] at *
  simp_all

theorem spec_newLocation_odd :
    ∀ (nb_steps k : Int) (l : Location),
    nb_steps % 2 ≠ 0 →
    Flocq.newLocation nb_steps k l =
      Flocq.newLocationOdd nb_steps k l := by
  intros
  dsimp only [Flocq.newLocation, Flocq.newLocationOdd] at *
  simp_all

theorem spec_fdivCore_quotient_lo :
    ∀ (beta : Radix) (fexp : Int → Int) (m1 e1 m2 e2 e : Int),
    e ≤ e1 - e2 →
    (Flocq.fdivCore beta fexp m1 e1 m2 e2 e).1 =
      (m1 * beta.val ^ (e1 - e2 - e).toNat) / m2 := by
  intros
  dsimp only [Flocq.fdivCore] at *
  simp_all

theorem spec_falign_exp_le :
    ∀ (β : Radix) (f1 f2 : FloatNum),
    f1.Fexp ≤ f2.Fexp →
    (Flocq.falign β f1 f2).2 = f1.Fexp := by
  intros
  dsimp only [Flocq.falign] at *
  simp_all

theorem spec_falign_left_mantissa_le :
    ∀ (β : Radix) (f1 f2 : FloatNum),
    f1.Fexp ≤ f2.Fexp →
    (Flocq.falign β f1 f2).1.1 = f1.Fnum := by
  intros
  dsimp only [Flocq.falign] at *
  simp_all

theorem spec_fplus_zero_left :
    ∀ (beta : Radix) (fexp : Int → Int) (f1 f2 : FloatNum),
    f1.Fnum = 0 →
    Flocq.fplus beta fexp f1 f2 = (f2.Fnum, f2.Fexp, Location.Exact) := by
  intros
  dsimp only [Flocq.fplus] at *
  simp_all

theorem spec_fplus_zero_right :
    ∀ (beta : Radix) (fexp : Int → Int) (f1 f2 : FloatNum),
    f1.Fnum ≠ 0 → f2.Fnum = 0 →
    Flocq.fplus beta fexp f1 f2 = (f1.Fnum, f1.Fexp, Location.Exact) := by
  intros
  dsimp only [Flocq.fplus] at *
  simp_all

theorem spec_truncate_passthrough :
    ∀ (β : Radix) (fexp : Int → Int) (m e : Int) (l : Location),
    fexp (Flocq.zdigits β m + e) ≤ e →
    Flocq.truncate β fexp (m, e, l) = (m, e, l) := by
  intros
  dsimp only [Flocq.zdigits, Flocq.truncate] at *
  simp_all

theorem spec_truncate_shifts :
    ∀ (β : Radix) (fexp : Int → Int) (m e : Int) (l : Location),
    fexp (Flocq.zdigits β m + e) > e →
    Flocq.truncate β fexp (m, e, l) =
      Flocq.truncateAux β (m, e, l) (fexp (Flocq.zdigits β m + e) - e) := by
  intros
  dsimp only [Flocq.zdigits, Flocq.truncate, Flocq.truncateAux] at *
  simp_all

theorem spec_truncateFIX_passthrough :
    ∀ (β : Radix) (emin m e : Int) (l : Location),
    emin ≤ e →
    Flocq.truncateFIX β emin (m, e, l) = (m, e, l) := by
  intros
  dsimp only [Flocq.truncateFIX] at *
  simp_all

theorem spec_truncateFIX_mantissa :
    ∀ (β : Radix) (emin m e : Int) (l : Location),
    emin > e →
    (Flocq.truncateFIX β emin (m, e, l)).1 =
      m / β.val ^ (emin - e).natAbs := by
  intros
  dsimp only [Flocq.truncateFIX] at *
  simp_all

theorem spec_truncateFIX_exponent :
    ∀ (β : Radix) (emin m e : Int) (l : Location),
    emin > e →
    (Flocq.truncateFIX β emin (m, e, l)).2.1 = emin := by
  intros
  dsimp only [Flocq.truncateFIX] at *
  simp_all

theorem spec_truncateFIX_location :
    ∀ (β : Radix) (emin m e : Int) (l : Location),
    emin > e →
    (Flocq.truncateFIX β emin (m, e, l)).2.2 =
      Flocq.newLocation
        (β.val ^ (emin - e).natAbs)
        (m % β.val ^ (emin - e).natAbs)
        l := by
  intros
  dsimp only [Flocq.truncateFIX, Flocq.newLocation] at *
  simp_all

theorem spec_digits2Pnat_pos :
    ∀ (n : Nat), n ≠ 0 → 0 < Flocq.digits2Pnat n := by
  intros
  dsimp only [Flocq.digits2Pnat] at *
  simp_all

theorem spec_zscale_zero :
    ∀ (r : Radix) (n : Int), Flocq.zscale r n 0 = n := by
  intros
  dsimp only [Flocq.zscale] at *
  simp_all

theorem spec_zscale_nonneg :
    ∀ (r : Radix) (n k : Int), 0 ≤ k →
    Flocq.zscale r n k = n * (r.val ^ k.toNat) := by
  intros
  dsimp only [Flocq.zscale] at *
  simp_all

theorem spec_zslice_empty :
    ∀ (r : Radix) (n k1 k2 : Int), k2 ≤ k1 → Flocq.zslice r n k1 k2 = 0 := by
  intros
  dsimp only [Flocq.zslice] at *
  simp_all

theorem spec_zdigits_opp :
    ∀ (r : Radix) (n : Int), Flocq.zdigits r (-n) = Flocq.zdigits r n := by
  intros
  dsimp only [Flocq.zdigits] at *
  simp_all

theorem spec_succ_opp :
    ∀ (beta : Radix) (fexp : Int → Int) [ValidExp fexp] (x : ℝ),
  Flocq.succ beta fexp (-x) = -(Flocq.pred beta fexp x) := by
  intros
  dsimp only [Flocq.succ, Flocq.pred] at *
  simp_all

theorem spec_zposDivEuclAux_small :
    ∀ (a b : Int), a < b → Flocq.zposDivEuclAux a b = (0, a) := by
  intros
  dsimp only [Flocq.zposDivEuclAux] at *
  simp_all

theorem spec_zposDivEuclAux_equal :
    ∀ (a b : Int), a = b → ¬ a < b → Flocq.zposDivEuclAux a b = (1, 0) := by
  intros
  dsimp only [Flocq.zposDivEuclAux] at *
  simp_all

theorem spec_pffFplus_zero_left :
    ∀ x : PffFloat, Flocq.pffFplus { num := 0, exp := x.exp } x = x := by
  intros
  dsimp only [Flocq.pffFplus] at *
  simp_all

theorem spec_pffFplus_zero_right :
    ∀ x : PffFloat, Flocq.pffFplus x { num := 0, exp := x.exp } = x := by
  intros
  dsimp only [Flocq.pffFplus] at *
  simp_all

theorem spec_pffMZlistAux_mem :
    ∀ (start : Int) (n : Nat) (k : Nat),
    k <= n → start + Int.ofNat k ∈ Flocq.pffMZlistAux start n := by
  intros
  dsimp only [Flocq.pffMZlistAux] at *
  simp_all

end FlocqCertificates
