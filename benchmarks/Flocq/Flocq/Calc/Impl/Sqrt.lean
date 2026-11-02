import Flocq.Core.Impl.Zaux
import Flocq.Core.Impl.Defs
import Flocq.Core.Impl.Digits
import Flocq.Calc.Impl.Bracket

-- !benchmark @start imports
import Mathlib.Data.Nat.Sqrt
-- !benchmark @end imports

/-!
# Flocq.Calc.Impl.Sqrt

Floating-point square root kernel, translated from the Coq source
`src/Calc/Sqrt.v`.

`fsqrtCore` is the low-level integer square root engine: given radix `beta`,
mantissa `m1`, and target exponents `e1` and `e`, it shifts the mantissa so
that the shifted value m1' = m1 · β^(e1−2e) has enough digits, computes the
integer square root q = ⌊√m1'⌋ and remainder r = m1' − q², and encodes the
rounding position as a `Location` (`Exact` when r = 0, `Inexact lt` when
r ≤ q, `Inexact gt` when r > q).

`fsqrt` is the high-level wrapper: it extracts the mantissa and exponent from
a `FloatNum`, computes the target exponent e = min(fexp(⌊e'/2⌋), ⌊e1/2⌋)
where e' = zdigits(β, m1) + e1 + 1, delegates to `fsqrtCore`, and returns
the full triple `(mantissa, exponent, location)`.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Implement only
the function bodies inside the `!benchmark code` markers.
-/

-- ── Spec helpers (curator-given vocabulary, DO NOT MODIFY) ────────────────────

/-- Floor division by 2, matching Coq's `Z.div2`.
    Lean `Int` division already rounds toward negative infinity for divisor 2. -/
def Flocq.zdiv2 (n : Int) : Int := n / 2

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────

/-- Signature for `fsqrtCore`: given a radix, mantissa `m1`, and exponents
    `e1` and `e`, compute the integer square root mantissa and the `Location`
    of the true square root relative to the returned floating-point number.
    Correctness requires `2 * e ≤ e1` and `0 < m1`. -/
abbrev FsqrtCoreSig := Radix → Int → Int → Int → Int × Location

/-- Signature for `fsqrt`: given a radix, exponent function `fexp`, and a
    `FloatNum`, compute `(mantissa, exponent, location)` for the square root.
    Correctness requires the input float to be positive. -/
abbrev FsqrtSig := Radix → (Int → Int) → FloatNum → Int × Int × Location

end Flocq

-- !benchmark @start global_aux
-- !benchmark @end global_aux

-- !benchmark @start code_aux def=fsqrtCore
-- Integer square root via Newton's method: computes ⌊√n⌋ for n : Nat.
-- The sequence x_{k+1} = ⌊(x_k + n/x_k)/2⌋ is eventually non-increasing
-- and stable at ⌊√n⌋. We give it (n + 2) steps of fuel which is more than
-- sufficient; in practice it converges in O(log n) iterations.
private def isqrtNewton (n : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel + 1, x =>
    if x = 0 then 0
    else
      let x' := (x + n / x) / 2
      if x' >= x then x
      else isqrtNewton n fuel x'

private def isqrt (n : Nat) : Nat :=
  if n = 0 then 0
  else isqrtNewton n (n + 2) n
private theorem newton_eq_iter (n fuel guess : Nat) (hf : guess ≤ fuel) :
    isqrtNewton n fuel guess = Nat.sqrt.iter n guess := by
  induction fuel generalizing guess with
  | zero =>
    have hg : guess = 0 := by omega
    subst guess
    rw [Nat.sqrt.iter]
    simp [isqrtNewton]
  | succ fuel ih =>
    rw [isqrtNewton]
    by_cases h0 : guess = 0
    · subst guess
      rw [Nat.sqrt.iter]
      simp
    · rw [if_neg h0]
      dsimp only
      by_cases hh : (guess + n / guess) / 2 < guess
      · rw [if_neg (Nat.not_le.mpr hh)]
        rw [Nat.sqrt.iter, dif_pos hh]
        exact ih _ (by omega)
      · rw [if_pos (Nat.le_of_not_gt hh)]
        rw [Nat.sqrt.iter, dif_neg hh]

theorem Flocq.isqrt_bounds (n : Nat) :
    isqrt n * isqrt n ≤ n ∧ n < (isqrt n + 1) * (isqrt n + 1) := by
  by_cases hn : n = 0
  · subst n
    simp [isqrt]
  · have heq : isqrt n = Nat.sqrt.iter n n := by
      simp only [isqrt, hn, ↓reduceIte]
      exact newton_eq_iter n (n + 2) n (by omega)
    rw [heq]
    exact ⟨Nat.sqrt.iter_sq_le n n, Nat.sqrt.lt_iter_succ_sq n n (lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_mul_self (n + 1)))⟩

-- !benchmark @end code_aux def=fsqrtCore

def Flocq.fsqrtCore : Flocq.FsqrtCoreSig :=
-- !benchmark @start code def=fsqrtCore
  fun beta m1 e1 e =>
    -- Shift mantissa: m1' = m1 * β^(e1 - 2*e).
    -- Correctness precondition ensures 2*e ≤ e1, so the shift exponent is non-negative.
    let shift := (e1 - 2 * e).toNat
    let m1' : Int := m1 * beta.val ^ shift
    -- Integer square root: q = ⌊√m1'⌋, r = m1' − q².
    -- isqrt computes ⌊√n⌋ for Nat; m1'.toNat = 0 for m1' < 0 (degenerate case).
    let q : Int := Int.ofNat (isqrt m1'.toNat)
    let r : Int := m1' - q * q
    -- Location encodes where the true square root sits relative to q · β^e:
    --   r = 0  → Exact (m1' is a perfect square)
    --   r ≤ q  → Inexact lt (true root is below midpoint of [q, q+1] interval)
    --   r > q  → Inexact gt (true root is above midpoint)
    let l : Location :=
      if r = 0 then Location.Exact
      else Location.Inexact (if r ≤ q then Ordering.lt else Ordering.gt)
    (q, l)
-- !benchmark @end code def=fsqrtCore

-- !benchmark @start code_aux def=fsqrt
-- !benchmark @end code_aux def=fsqrt

def Flocq.fsqrt : Flocq.FsqrtSig :=
-- !benchmark @start code def=fsqrt
  fun beta fexp x =>
    let m1 := x.Fnum
    let e1 := x.Fexp
    -- e' = Zdigits β m1 + e1 + 1: magnitude estimate for the square root exponent.
    let e' : Int := Flocq.zdigits beta m1 + e1 + 1
    -- Target exponent: minimum of fexp(⌊e'/2⌋) and ⌊e1/2⌋.
    -- zdiv2 implements Coq's Z.div2 (floor division by 2).
    let e : Int := min (fexp (Flocq.zdiv2 e')) (Flocq.zdiv2 e1)
    -- Delegate to the core square root kernel.
    let (m, l) := Flocq.fsqrtCore beta m1 e1 e
    (m, e, l)
-- !benchmark @end code def=fsqrt
