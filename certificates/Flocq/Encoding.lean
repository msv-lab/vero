import Flocq.IEEE754.Impl.PrimFloat
import Flocq.IEEE754.Impl.Bits

namespace FlocqCertificates

theorem b2Prim_minExponent_subnormal (s : Bool) (m : Nat) (hm : m < 2 ^ 52) :
    Flocq.b2Prim (.finite s m (-1074)) =
      Float.ofBits ((if s then 0x8000000000000000 else 0 : UInt64) |||
        (m.toUInt64 &&& 0x000FFFFFFFFFFFFF)) := by
  have hm' : m < 4503599627370496 := by norm_num at hm; exact hm
  simp [Flocq.b2Prim, hm']

theorem b2Prim_minExponent_normal (s : Bool) (m : Nat) (hm : 2 ^ 52 ≤ m) :
    Flocq.b2Prim (.finite s m (-1074)) =
      Float.ofBits ((if s then 0x8000000000000000 else 0 : UInt64) |||
        ((1 : UInt64) <<< 52) ||| (m.toUInt64 &&& 0x000FFFFFFFFFFFFF)) := by
  have hm' : ¬ m < 4503599627370496 := by norm_num at hm; omega
  simp [Flocq.b2Prim, hm']

theorem b2Prim_smallest_normal :
    Flocq.b2Prim (.finite false (2 ^ 52) (-1074)) =
      Float.ofBits 0x0010000000000000 := by rfl

theorem b2Prim_largest_subnormal :
    Flocq.b2Prim (.finite false (2 ^ 52 - 1) (-1074)) =
      Float.ofBits 0x000FFFFFFFFFFFFF := by rfl

theorem bits_negativeZero :
    Flocq.bitsOfBinaryFloat 52 11 (.zero true) = 9223372036854775808 := by rfl

theorem split_ieeeNegativeZero :
    Flocq.splitBits 52 11 9223372036854775808 = (true, 0, 0) := by rfl

end FlocqCertificates

#print axioms FlocqCertificates.b2Prim_minExponent_subnormal
#print axioms FlocqCertificates.b2Prim_minExponent_normal
#print axioms FlocqCertificates.b2Prim_smallest_normal
#print axioms FlocqCertificates.b2Prim_largest_subnormal
