import Verdict.Spec.PolicyStandard

namespace VerdictCertificates.Counterexamples

/-- Original frozen Chrome obligations, retained as kernel-checked counterexamples. -/
def oldChromeBasicConstraintsCA : Prop :=
  ∀ env, Verdict.Policy.Standard.BasicConstraintsCA (Verdict.chromeValidChain env)
def oldChromeTimeValidity : Prop :=
  ∀ env, Verdict.Policy.Standard.TimeValidity (Verdict.chromeValidChain env)
def oldChromeValidVersion : Prop :=
  ∀ env chain task, Verdict.chromeValidChain env chain task = true →
    ∀ i, i < chain.length → chain[i]!.allExts.isSome → chain[i]!.version ≥ 3
open Verdict.Policy

def chromeEnv : ChromePolicyEnv := default

def task : PolicyTask := { hostname := none, purpose := .serverAuth, now := 1 }

def cert : AbstractCertificate := {
  (default : AbstractCertificate) with
  version := 2
  subjectKey := .other
  notBefore := 0
  notAfter := 2
  subject := { rdns := [[{ oid := "", value := "" }]] }
  sigAlgInner := { id := "1.2.840.113549.1.1.11", bytes := "" }
  sigAlgOuter := { id := "1.2.840.113549.1.1.11", bytes := "" }
}

theorem chrome_base_accepts : Verdict.chromeValidChain chromeEnv [cert, cert] task = true := by
  decide

theorem chrome_basicConstraintsCA_refuted : ¬ oldChromeBasicConstraintsCA := by
  intro h
  have impossible := h chromeEnv [cert, cert] task chrome_base_accepts 1 (by decide) (by decide)
  change false = true at impossible
  contradiction

def expiredRoot : AbstractCertificate := { cert with notBefore := 2, notAfter := 0 }

theorem chrome_expiredRoot_accepts : Verdict.chromeValidChain chromeEnv [cert, expiredRoot] task = true := by
  decide

theorem chrome_timeValidity_refuted : ¬ oldChromeTimeValidity := by
  intro h
  have impossible := (h chromeEnv [cert, expiredRoot] task chrome_expiredRoot_accepts 1 (by decide)).1
  change (2 : UInt64) ≤ 1 at impossible
  exact (by decide : ¬ (2 : UInt64) ≤ 1) impossible

def v3WithExtensions : AbstractCertificate := { cert with allExts := some [] }

theorem chrome_v3_accepts : Verdict.chromeValidChain chromeEnv [v3WithExtensions, cert] task = true := by
  decide

theorem chrome_validVersion_refuted : ¬ oldChromeValidVersion := by
  intro h
  have impossible := h chromeEnv [v3WithExtensions, cert] task chrome_v3_accepts 0 (by decide) (by decide)
  change (2 : UInt32) ≥ 3 at impossible
  exact (by decide : ¬ (2 : UInt32) ≥ 3) impossible

end VerdictCertificates.Counterexamples
