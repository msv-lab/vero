import Verdict.Spec.PolicyChrome
import Verdict.Spec.PolicyFirefox
import Verdict.Spec.PolicyOpenSSL
import Verdict.Spec.PolicyStandard

namespace VerdictCertificates.Policy
open Verdict.Policy
open Verdict.Policy.Standard

private theorem and_true {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem chrome_valid_chain_min_length :
  ∀ (env : Verdict.Policy.ChromePolicyEnv)
      (chain : List Verdict.Policy.AbstractCertificate)
      (task : Verdict.Policy.PolicyTask),
      Verdict.chromeValidChain env chain task = true →
      chain.length ≥ 2 := by
  intro env chain task h
  exact of_decide_eq_true (and_true (and_true (and_true (and_true h).1).1).1).1

theorem chrome_valid_chain_leaf :
  ∀ (env : Verdict.Policy.ChromePolicyEnv)
      (chain : List Verdict.Policy.AbstractCertificate)
      (task : Verdict.Policy.PolicyTask),
      Verdict.chromeValidChain env chain task = true →
      chain.length ≥ 2 →
      Verdict.chromeCertVerifiedLeaf env task
        chain[0]! chain[chain.length - 1]! = true := by
  intro env chain task h _
  exact (and_true (and_true (and_true (and_true h).1).1).1).2

theorem chrome_valid_chain_name_constraints :
  ∀ (env : Verdict.Policy.ChromePolicyEnv)
      (chain : List Verdict.Policy.AbstractCertificate)
      (task : Verdict.Policy.PolicyTask),
      Verdict.chromeValidChain env chain task = true →
      Verdict.chromeCheckAllNameConstraints chain = true := by
  intro env chain task h
  exact (and_true (and_true h).2).1

theorem chrome_is_valid_pki_no_dsa :
  ∀ (cert : Verdict.Policy.AbstractCertificate) (p q g : Nat),
      cert.subjectKey = .dsa p q g →
      Verdict.Policy.Chrome.isValidPki cert = false := by
  intro cert p q g h
  simp [Chrome.isValidPki, h]

theorem chrome_strong_signature_rsa_sha256 :
  Verdict.Policy.Chrome.strongSignature "1.2.840.113549.1.1.11" = true := by decide

theorem firefox_valid_chain_min_length :
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv)
      (chain : List Verdict.Policy.AbstractCertificate)
      (task : Verdict.Policy.PolicyTask),
      Verdict.firefoxValidChain env chain task = true →
      chain.length ≥ 2 := by
  intro env chain task h
  have h := (and_true (and_true (and_true (and_true h).1).1).1).1
  exact of_decide_eq_true h

theorem firefox_valid_chain_name_constraints :
  ∀ (env : Verdict.Policy.FirefoxPolicyEnv)
      (chain : List Verdict.Policy.AbstractCertificate)
      (task : Verdict.Policy.PolicyTask),
      Verdict.firefoxValidChain env chain task = true →
      Verdict.firefoxCheckAllNameConstraints chain = true := by
  intro env chain task h
  exact (and_true h).2

theorem firefox_likely_issued_decompose :
  ∀ (issuer subject : Verdict.Policy.AbstractCertificate),
      Verdict.firefoxLikelyIssued issuer subject = true →
      Verdict.Policy.sameDN issuer.subject subject.issuer false = true ∧
      Verdict.Policy.checkAuthKeyId issuer subject = true := by
  intro issuer subject h
  exact and_true h

theorem firefox_check_eku_leaf_none :
  ∀ (cert : Verdict.Policy.AbstractCertificate),
      cert.extExtendedKeyUsage = none →
      Verdict.Policy.Firefox.checkEkuLeaf cert = true := by
  intro cert h
  simp [Firefox.checkEkuLeaf, h]

theorem firefox_check_key_usage_leaf_none :
  ∀ (cert : Verdict.Policy.AbstractCertificate),
      cert.extKeyUsage = none →
      Verdict.Policy.Firefox.checkKeyUsageLeaf cert = true := by
  intro cert h
  simp [Firefox.checkKeyUsageLeaf, h]

theorem openssl_valid_chain_min_length :
  ∀ (chain : List Verdict.Policy.AbstractCertificate)
      (task : Verdict.Policy.PolicyTask),
      Verdict.opensslValidChain chain task = true →
      chain.length ≥ 2 := by
  intro chain task h
  have h := (and_true (and_true (and_true (and_true (and_true h).1).1).1).1).1
  exact of_decide_eq_true h

theorem openssl_valid_chain_hostname :
  ∀ (chain : List Verdict.Policy.AbstractCertificate)
      (task : Verdict.Policy.PolicyTask) (hostname : String),
      Verdict.opensslValidChain chain task = true →
      task.hostname = some hostname →
      Verdict.opensslCheckHostname chain[0]! hostname = true := by
  intro chain task hostname h hh
  have h := (and_true h).2
  simpa only [hh] using h

theorem openssl_check_cert_key_level_rsa :
  ∀ (cert : Verdict.Policy.AbstractCertificate) (n : Nat),
      cert.subjectKey = .rsa n → n ≥ 1024 →
      Verdict.Policy.OpenSSL.checkCertKeyLevel cert = true := by
  intro cert n h hn
  simp [OpenSSL.checkCertKeyLevel, h, hn]

theorem openssl_check_cert_time_valid :
  ∀ (cert : Verdict.Policy.AbstractCertificate) (now : UInt64),
      cert.notBefore ≤ now → cert.notAfter > now →
      Verdict.Policy.OpenSSL.checkCertTime cert now = true := by
  intro cert now h₁ h₂
  simp [OpenSSL.checkCertTime, h₁, h₂]

theorem openssl_check_san_none :
  ∀ (cert : Verdict.Policy.AbstractCertificate),
      cert.extSubjectAltName = none →
      Verdict.Policy.OpenSSL.checkSan cert = true := by
  intro cert h
  simp [OpenSSL.checkSan, h]

end VerdictCertificates.Policy
