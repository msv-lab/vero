import Flocq.IEEE754.Impl.Bits
import Flocq.IEEE754.Impl.PrimFloat

namespace FlocqCertificates

-- These statements concern the unrestricted old constructor domain, not the amended specs.

theorem bits_nan_zero_collision (mw ew : Int) (s : Bool) :
    Flocq.bitsOfBinaryFloat mw ew (.nan s 0) =
      Flocq.bitsOfBinaryFloat mw ew (.inf s) := by
  simp [Flocq.bitsOfBinaryFloat]

theorem bits_no_leftInverse (mw ew : Int)
    (decode : Int → BinaryFloat (mw + 1) ((2 : Int) ^ (ew - 1).toNat)) :
    ¬ Function.LeftInverse decode (Flocq.bitsOfBinaryFloat mw ew) := by
  intro h
  have hn := h (BinaryFloat.nan false 0)
  have hi := h (BinaryFloat.inf false)
  rw [bits_nan_zero_collision] at hn
  have bad : BinaryFloat.nan (prec := mw + 1)
      (emax := (2 : Int) ^ (ew - 1).toNat) false 0 = BinaryFloat.inf false :=
    hn.symm.trans hi
  cases bad

theorem b2Prim_zero_collision (s : Bool) :
    Flocq.b2Prim (.finite s 0 (-1074)) = Flocq.b2Prim (.zero s) := by
  cases s <;> rfl

theorem b2Prim_no_leftInverse (decode : Float → BinaryFloat 53 1024) :
    ¬ Function.LeftInverse decode Flocq.b2Prim := by
  intro h
  have hf := h (BinaryFloat.finite false 0 (-1074))
  have hz := h (BinaryFloat.zero false)
  rw [b2Prim_zero_collision] at hf
  have bad : BinaryFloat.finite (prec := 53) (emax := 1024) false 0 (-1074) =
      BinaryFloat.zero false := hf.symm.trans hz
  cases bad

end FlocqCertificates

#print axioms FlocqCertificates.bits_no_leftInverse
#print axioms FlocqCertificates.b2Prim_no_leftInverse
