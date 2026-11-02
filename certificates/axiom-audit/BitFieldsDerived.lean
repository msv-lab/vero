set_option autoImplicit false
namespace CanonicalAxiomAudit
theorem uint64_bv (a : BitVec 64) : (a.toNat.toUInt64.toBitVec) = a := by simp
theorem bv_uint64 (a : UInt64) : (a.toBitVec.toNat.toUInt64) = a := by simp
theorem uint32_bv (a : BitVec 32) : (a.toNat.toUInt32.toBitVec) = a := by simp
theorem bv_uint32 (a : UInt32) : (a.toBitVec.toNat.toUInt32) = a := by simp
theorem uint16_bv (a : BitVec 16) : (a.toNat.toUInt16.toBitVec) = a := by simp
theorem bv_uint16 (a : UInt16) : (a.toBitVec.toNat.toUInt16) = a := by simp
theorem uint8_bv (a : BitVec 8) : (a.toNat.toUInt8.toBitVec) = a := by simp
theorem bv_uint8 (a : UInt8) : (a.toBitVec.toNat.toUInt8) = a := by simp

#print axioms uint64_bv
#print axioms bv_uint64
#print axioms uint32_bv
#print axioms bv_uint32
#print axioms uint16_bv
#print axioms bv_uint16
#print axioms uint8_bv
#print axioms bv_uint8
end CanonicalAxiomAudit
