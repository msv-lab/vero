import Std
import Verdict.Spec.Base64
import Verdict.Spec.Parser
import Verdict.Spec.Issue
import Verdict.Spec.Validator
import Verdict.Spec.PolicyChrome
import Verdict.Spec.PolicyFirefox
import Verdict.Spec.PolicyOpenSSL
import Verdict.Spec.PolicyCommon
import Verdict.Spec.PolicyStandard

namespace VerdictCertificates

theorem charToBits_upper :
  ∀ (c : UInt8),
      c ≥ 0x41 → c ≤ 0x5A →
      Verdict.charToBits c = some (some (c - 0x41)) := by
  intro c h₁ h₂
  simp [Verdict.charToBits, h₁, h₂]

theorem charToBits_lower :
  ∀ (c : UInt8),
      c ≥ 0x61 → c ≤ 0x7A →
      Verdict.charToBits c = some (some (c - 0x61 + 26)) := by
  intro c h₁ h₂
  have h₀ : ¬ (c ≥ 0x41 ∧ c ≤ 0x5A) := by (simp [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_sub, UInt8.toNat_add] at *; omega)
  simp [Verdict.charToBits, h₀, h₁, h₂]

theorem charToBits_digit :
  ∀ (c : UInt8),
      c ≥ 0x30 → c ≤ 0x39 →
      Verdict.charToBits c = some (some (c - 0x30 + 52)) := by
  intro c h₁ h₂
  have h₀ : ¬ (c ≥ 0x41 ∧ c ≤ 0x5A) := by (simp [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_sub, UInt8.toNat_add] at *; omega)
  have h₃ : ¬ (c ≥ 0x61 ∧ c ≤ 0x7A) := by (simp [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_sub, UInt8.toNat_add] at *; omega)
  simp [Verdict.charToBits, h₀, h₁, h₂, h₃]

theorem charToBits_plus :
  Verdict.charToBits 0x2B = some (some 62) := by rfl
theorem charToBits_slash :
  Verdict.charToBits 0x2F = some (some 63) := by rfl
theorem charToBits_padding :
  Verdict.charToBits 0x3D = some none := by rfl

theorem charToBits_reject :
  ∀ (c : UInt8),
      (c < 0x2B ∨ (c > 0x2B ∧ c < 0x2F) ∨
       (c > 0x39 ∧ c < 0x3D) ∨ (c > 0x3D ∧ c < 0x41) ∨
       (c > 0x5A ∧ c < 0x61) ∨ c > 0x7A) →
      Verdict.charToBits c = none := by
  intro c h
  have h₁ : ¬ (c ≥ 0x41 ∧ c ≤ 0x5A) := by (simp [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_sub, UInt8.toNat_add] at *; omega)
  have h₂ : ¬ (c ≥ 0x61 ∧ c ≤ 0x7A) := by (simp [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_sub, UInt8.toNat_add] at *; omega)
  have h₃ : ¬ (c ≥ 0x30 ∧ c ≤ 0x39) := by (simp [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_sub, UInt8.toNat_add] at *; omega)
  have h₄ : c ≠ 0x2B := by (simp [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_sub, UInt8.toNat_add] at *; omega)
  have h₅ : c ≠ 0x2F := by (simp [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_sub, UInt8.toNat_add] at *; omega)
  have h₆ : c ≠ 0x3D := by (simp [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_sub, UInt8.toNat_add] at *; omega)
  simp [Verdict.charToBits, h₁, h₂, h₃, h₄, h₅, h₆]
theorem decode6Bits_length :
  ∀ (a b c d : UInt8), (Verdict.decode6Bits a b c d).length = 3 := by
  intro a b c d; rfl

theorem decode6Bits_byte0 :
  ∀ (a b c d : UInt8),
      (Verdict.decode6Bits a b c d)[0]? = some ((a <<< 2) ||| (b >>> 4)) := by
  intro a b c d; rfl

theorem decode6Bits_byte1 :
  ∀ (a b c d : UInt8),
      (Verdict.decode6Bits a b c d)[1]? = some ((b <<< 4) ||| (c >>> 2)) := by
  intro a b c d; rfl

theorem decode6Bits_byte2 :
  ∀ (a b c d : UInt8),
      (Verdict.decode6Bits a b c d)[2]? = some ((c <<< 6) ||| d) := by
  intro a b c d; rfl

theorem parseX509Base64_pipeline :
  ∀ (input : Verdict.Bytes),
      Verdict.parseX509Base64 input =
        (Verdict.decodeBase64 input >>= Verdict.parseX509Der) := by
  intro input; rfl

theorem decodeBase64_empty :
  Verdict.decodeBase64 [] = some [] := by rfl

theorem charToBits_bound :
  ∀ (c : UInt8) (v : UInt8),
      Verdict.charToBits c = some (some v) →
      v ≤ 63 := by
  intro c v h
  simp only [Verdict.charToBits] at h
  split at h
  all_goals try (split at h)
  all_goals try (split at h)
  all_goals try (split at h)
  all_goals try (split at h)
  all_goals try (split at h)
  all_goals simp_all
  all_goals (simp [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_sub, UInt8.toNat_add] at *; omega)
theorem decodeBase64_allPadding :
  Verdict.decodeBase64 [0x3D, 0x3D, 0x3D, 0x3D] = none := by rfl

theorem parseX509Der_deterministic :
  ∀ (der : Verdict.Bytes) (c1 c2 : Verdict.Certificate),
      Verdict.parseX509Der der = some c1 →
      Verdict.parseX509Der der = some c2 →
      c1 = c2 := by
  intro der c₁ c₂ h₁ h₂
  exact Option.some.inj (h₁.symm.trans h₂)

theorem issuedByRaw_signature :
  ∀ (issuer subject : Verdict.Certificate),
      Verdict.issuedByRaw issuer subject = true →
      Verdict.verifySignature issuer subject = true := by
  intro issuer subject h
  exact (Bool.and_eq_true_iff.mp h).2

theorem issuedByRaw_names :
  ∀ (issuer subject : Verdict.Certificate),
      Verdict.issuedByRaw issuer subject = true →
      issuer.cert.subject = subject.cert.issuer := by
  intro issuer subject h
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1

theorem isSimplePath_nil :
  Verdict.isSimplePath [] = true := by rfl

theorem isSimplePath_singleton :
  ∀ (i : Nat), Verdict.isSimplePath [i] = true := by
  intro i; simp [Verdict.isSimplePath, List.eraseDups_cons]

theorem pathInBounds_forall :
  ∀ (path : Verdict.BundlePath) (bundleLen : Nat),
      Verdict.pathInBounds path bundleLen = true →
      ∀ i, i ∈ path → i < bundleLen := by
  intro path len h i hi
  exact of_decide_eq_true ((List.all_eq_true.mp h) i hi)

theorem validator_empty :
  ∀ (rootsB64 : List Verdict.Bytes) (task : Verdict.Task),
      (Verdict.validateX509Base64 rootsB64 [] task).isOk = false := by
  intro roots task; rfl

theorem chrome_strong_rsa :
  Verdict.Policy.Chrome.strongSignature "1.2.840.113549.1.1.11" = true := by rfl

end VerdictCertificates
