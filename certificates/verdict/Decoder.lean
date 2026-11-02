import Std
import Verdict.Spec.Base64
import Verdict.Spec.Parser

namespace VerdictCertificates.Decoder

private theorem decode_shape (input : Verdict.Bytes) (output : Verdict.Bytes)
    (h : Verdict.decodeBase64 input = some output) :
    input.length % 4 = 0 ∧ output.length * 4 = input.length * 3 := by
  change Verdict.decodeBase64.go input = some output at h
  induction input using Verdict.decodeBase64.go.induct generalizing output with
  | case1 => simp_all [Verdict.decodeBase64.go]
  | case2 a b c d rest ih =>
    simp only [Verdict.decodeBase64.go] at h
    cases ha : Verdict.charToBits a with
    | none => simp [ha] at h
    | some av =>
      cases av with
      | none => simp [ha] at h
      | some av =>
        cases hb : Verdict.charToBits b with
        | none => simp [ha, hb] at h
        | some bv =>
          cases bv with
          | none => simp [ha, hb] at h
          | some bv =>
            cases hc : Verdict.charToBits c with
            | none => simp [ha, hb, hc] at h
            | some cv =>
              cases cv with
              | none => simp [ha, hb, hc] at h
              | some cv =>
                cases hd : Verdict.charToBits d with
                | none => simp [ha, hb, hc, hd] at h
                | some dv =>
                  cases dv with
                  | none => simp [ha, hb, hc, hd] at h
                  | some dv =>
                    cases ht : Verdict.decodeBase64.go rest with
                    | none => simp [ha, hb, hc, hd, ht] at h
                    | some out =>
                      have hi := ih out ht
                      simp [ha, hb, hc, hd, ht] at h
                      subst output
                      simp [Verdict.decode6Bits, List.length_append, Nat.add_mod, hi]
                      omega
  | case3 a => simp_all [Verdict.decodeBase64.go]

theorem decodeBase64_length :
  ∀ (input : Verdict.Bytes) (output : Verdict.Bytes),
      Verdict.decodeBase64 input = some output →
      input.length % 4 = 0 →
      output.length * 4 = input.length * 3 := by
  intro input output h _
  exact (decode_shape input output h).2

theorem decodeBase64_multiple :
  ∀ (input output : Verdict.Bytes),
      Verdict.decodeBase64 input = some output →
      input.length % 4 = 0 := by
  intro input output h
  exact (decode_shape input output h).1

private theorem hex_fold (data : Verdict.Bytes) (acc : String) :
    data.foldl (fun result byte =>
      (result.push (Verdict.hexUpperDigit (byte >>> 4))).push (Verdict.hexUpperDigit (byte &&& 0x0f))) acc =
      acc ++ Verdict.specToHexUpper data := by
  induction data generalizing acc with
  | nil => simp [Verdict.specToHexUpper]
  | cons b rest ih =>
    have h₁ : b >>> 4 = b / 16 := by
      apply UInt8.toNat_inj.mp
      simp [UInt8.toNat_shiftRight, UInt8.toNat_div, Nat.shiftRight_eq_div_pow]
    have h₂ : b &&& 0x0f = b % 16 := by
      apply UInt8.toNat_inj.mp
      simp only [UInt8.toNat_and, UInt8.toNat_mod]
      simpa using Nat.and_two_pow_sub_one_eq_mod b.toNat 4
    rw [List.foldl_cons, ih]
    apply String.toList_injective
    simp [Verdict.specToHexUpper, String.push_eq_append, String.toList_append, List.append_assoc,
      h₁, h₂, String.append_assoc, -String.append_singleton]

theorem hex_upper_agreement :
  ∀ (data : Verdict.Bytes),
      Verdict.toHexUpper data = Verdict.specToHexUpper data := by
  intro data
  simpa [Verdict.toHexUpper] using hex_fold data ""

end VerdictCertificates.Decoder
