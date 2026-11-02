import Flocq.IEEE754.Impl.Binary

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Flocq.IEEE754.Impl.PrimFloat

Interface between Flocq's `BinaryFloat 53 1024` and Lean's native `Float`
(IEEE 754 binary64), translated from the Coq source `src/IEEE754/PrimFloat.v`.

The two API functions form a round-trip isomorphism for well-formed IEEE 754
binary64 values:

- `prim2B (x : Float) : BinaryFloat 53 1024` — decode a native float into
  the Flocq inductive by extracting the IEEE 754 bit fields (sign, biased
  exponent, mantissa) via `Float.toBits`.

- `b2Prim (x : BinaryFloat 53 1024) : Float` — encode a Flocq BinaryFloat
  back to a native float by reconstructing the IEEE 754 bit pattern and
  calling `Float.ofBits`.

Types and signatures are fixed vocabulary (DO NOT MODIFY). Implement only the
function bodies inside the `!benchmark code` markers.
-/

-- !benchmark @start global_aux
-- !benchmark @end global_aux

namespace Flocq

-- ── API signatures (DO NOT MODIFY) ───────────────────────────────────────────

/-- Signature for `b2Prim`: convert a Flocq binary64 to Lean's native Float. -/
abbrev B2PrimSig := BinaryFloat 53 1024 → Float

/-- Signature for `prim2B`: convert Lean's native Float to a Flocq binary64. -/
abbrev Prim2BSig := Float → BinaryFloat 53 1024

end Flocq

-- ── Implementation stubs (LLM task) ──────────────────────────────────────────

-- !benchmark @start code_aux def=b2Prim
-- !benchmark @end code_aux def=b2Prim

def Flocq.b2Prim : Flocq.B2PrimSig :=
-- !benchmark @start code def=b2Prim
  fun (x : BinaryFloat 53 1024) =>
    match x with
    | BinaryFloat.zero s =>
      Float.ofBits (if s then (0x8000000000000000 : UInt64) else (0x0000000000000000 : UInt64))
    | BinaryFloat.inf s =>
      Float.ofBits (if s then (0xFFF0000000000000 : UInt64) else (0x7FF0000000000000 : UInt64))
    | BinaryFloat.nan _ _ =>
      -- PrimFloat.v uses BinarySingleNaN: the native interface has one canonical NaN.
      Float.ofBits 0x7FF8000000000000
    | BinaryFloat.finite s m e =>
      -- Finite: reconstruct sign, biased exponent, and mantissa bits.
      -- Subnormal (e = -1074 and m < 2^52): exponent field = 0, mantissa = m.
      -- Normal (including e = -1074 and m ≥ 2^52): biased_exp = e + 1075,
      -- with the implicit leading bit (bit 52) cleared.
      let signBit : UInt64 := if s then 0x8000000000000000 else 0
      if e == (-1074 : Int) && m < 2 ^ 52 then
        -- Subnormal or zero-mantissa edge case: exponent field is 0.
        let frac : UInt64 := m.toUInt64 &&& 0x000FFFFFFFFFFFFF
        Float.ofBits (signBit ||| frac)
      else
        let biasedExp : Int := e + 1075
        if biasedExp ≤ 0 ∨ biasedExp ≥ (0x7FF : Int) then
          -- Exponent out of binary64 range: map to ±infinity as fallback.
          Float.ofBits (signBit ||| 0x7FF0000000000000)
        else
          -- Normal: strip the implicit leading bit from the mantissa.
          let frac : UInt64 := m.toUInt64 &&& 0x000FFFFFFFFFFFFF
          let expBits : UInt64 := biasedExp.toNat.toUInt64 <<< 52
          Float.ofBits (signBit ||| expBits ||| frac)
-- !benchmark @end code def=b2Prim

-- !benchmark @start code_aux def=prim2B
-- !benchmark @end code_aux def=prim2B

def Flocq.prim2B : Flocq.Prim2BSig :=
-- !benchmark @start code def=prim2B
  fun (x : Float) =>
    -- Decode the IEEE 754 binary64 bit pattern.
    -- Layout (64 bits): [63: sign] [62-52: biased_exp (11 bits)] [51-0: frac (52 bits)]
    let bits : UInt64 := x.toBits
    let s    : Bool   := bits >>> 63 != 0
    let e    : UInt64 := (bits >>> 52) &&& 0x7FF
    let f    : UInt64 := bits &&& 0x000FFFFFFFFFFFFF
    if e == 0x7FF then
      -- Exponent all 1s: NaN or infinity.
      if f == 0 then BinaryFloat.inf s
      else BinaryFloat.nan false 1
    else if e == 0 then
      -- Exponent zero: subnormal or zero.
      if f == 0 then BinaryFloat.zero s
      else BinaryFloat.finite s f.toNat (-1074 : Int)
    else
      -- Normal: mantissa includes implicit leading 1 (bit 52).
      -- Flocq exponent = biased_exp − 1023 − 52 = biased_exp − 1075.
      BinaryFloat.finite s (2 ^ 52 + f.toNat) ((e.toNat : Int) - 1075)
-- !benchmark @end code def=prim2B
