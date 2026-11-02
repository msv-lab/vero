-- !benchmark @start imports
-- !benchmark @end imports

/-!
# VerifiedBitmasks.Impl.BitFieldsAxioms

Round-trip cast axioms between bitvector types (`BitVec n`) and the
corresponding unsigned-integer machine types (`UInt64`, `UInt32`,
`UInt16`, `UInt8`).

These round-trip identities are proved using Lean's `Std` cast simp lemmas.

Translated from `src/BitFields/Spec/BitFields.s.dfy` (`module BitFieldsAxioms`).

DO NOT MODIFY types or definitions — these are the fixed vocabulary.
-/

-- ── Spec helpers (frozen theorems, curator-given, no markers) ──────────────

/-- Converting a `BitVec 64` to `UInt64` and back yields the original bitvector. -/
theorem axiom_as_uint64_as_bv64 (a : BitVec 64) :
    (a.toNat.toUInt64.toBitVec) = a := by simp

/-- Converting a `UInt64` to `BitVec 64` and back yields the original value. -/
theorem axiom_as_bv64_as_uint64 (a : UInt64) :
    (a.toBitVec.toNat.toUInt64) = a := by simp

/-- Converting a `BitVec 32` to `UInt32` and back yields the original bitvector. -/
theorem axiom_as_uint32_as_bv32 (a : BitVec 32) :
    (a.toNat.toUInt32.toBitVec) = a := by simp

/-- Converting a `UInt32` to `BitVec 32` and back yields the original value. -/
theorem axiom_as_bv32_as_uint32 (a : UInt32) :
    (a.toBitVec.toNat.toUInt32) = a := by simp

/-- Converting a `BitVec 16` to `UInt16` and back yields the original bitvector. -/
theorem axiom_as_uint16_as_bv16 (a : BitVec 16) :
    (a.toNat.toUInt16.toBitVec) = a := by simp

/-- Converting a `UInt16` to `BitVec 16` and back yields the original value. -/
theorem axiom_as_bv16_as_uint16 (a : UInt16) :
    (a.toBitVec.toNat.toUInt16) = a := by simp

/-- Converting a `BitVec 8` to `UInt8` and back yields the original bitvector. -/
theorem axiom_as_uint8_as_bv8 (a : BitVec 8) :
    (a.toNat.toUInt8.toBitVec) = a := by simp

/-- Converting a `UInt8` to `BitVec 8` and back yields the original value. -/
theorem axiom_as_bv8_as_uint8 (a : UInt8) :
    (a.toBitVec.toNat.toUInt8) = a := by simp
