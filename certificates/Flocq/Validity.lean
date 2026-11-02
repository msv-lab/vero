import Flocq.IEEE754.Impl.Bits
import Flocq.IEEE754.Impl.PrimFloat

namespace FlocqCertificates

theorem finiteZero_invalid :
    ¬ BinaryFloat.Valid 53 1024 (.finite false 0 (-1074)) := by
  decide

theorem nanZero_invalid :
    ¬ BinaryFloat.Valid 53 1024 (.nan false 0) := by
  decide

theorem smallestNormal_valid :
    BinaryFloat.Valid 53 1024 (.finite false (2 ^ 52) (-1074)) := by
  decide

theorem largestSubnormal_valid :
    BinaryFloat.Valid 53 1024 (.finite false (2 ^ 52 - 1) (-1074)) := by
  decide

theorem negativeZero_valid :
    BinaryFloat.Valid 53 1024 (.zero true) := by trivial

theorem singleNaN_canonical :
    BinaryFloat.Valid 53 1024 (.nan false 1) ∧
      BinaryFloat.SingleNaN (.nan (prec := 53) (emax := 1024) false 1) := by
  norm_num [BinaryFloat.Valid, BinaryFloat.SingleNaN]

theorem b2Prim_nan_canonical (s : Bool) (payload : Nat) :
    Flocq.b2Prim (.nan s payload) = Float.ofBits 0x7FF8000000000000 := by rfl

theorem validBinary_eq_decide (prec emax : Int) (x : BinaryFloat prec emax) :
    Flocq.validBinary prec emax x = decide (BinaryFloat.Valid prec emax x) := by rfl

end FlocqCertificates

#print axioms FlocqCertificates.finiteZero_invalid
#print axioms FlocqCertificates.nanZero_invalid
#print axioms FlocqCertificates.smallestNormal_valid
#print axioms FlocqCertificates.largestSubnormal_valid
#print axioms FlocqCertificates.negativeZero_valid
#print axioms FlocqCertificates.singleNaN_canonical
#print axioms FlocqCertificates.b2Prim_nan_canonical
#print axioms FlocqCertificates.validBinary_eq_decide
