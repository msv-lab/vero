import Verdict.Impl.PolicyCommon
import Verdict.Impl.PolicyChrome

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.PolicyFirefox

Lean 4 port of `verdict/src/policy/firefox.rs` — the Firefox
NSS-based certificate validation policy. Ports
`verdict_old/Verdict/Policy/Firefox.lean` into the new-format layout.

Shape:

* Curator-given: `FirefoxPolicyEnv` struct and the five helper
  predicates (`checkEkuLeaf`, `checkKeyUsageLeaf`,
  `checkKeyUsageIntermediate`, `strongSignature`, `sigAlgMatch`)
  live in `namespace Verdict.Policy.Firefox`. The last two are
  re-exports of their Chrome counterparts. Each helper takes
  `Verdict.Policy.AbstractCertificate` (not the parser-layer
  `Verdict.Certificate`).
* Benchmark tasks: six `!benchmark code` stubs
  (`firefoxCertVerifiedLeaf`, `firefoxCertVerifiedIntermediate`,
  `firefoxCertVerifiedRoot`, `firefoxCheckAllNameConstraints`,
  `firefoxLikelyIssued`, `firefoxValidChain`) flat-namespaced under
  `Verdict` with matching `*Sig` type abbreviations. Signatures
  use `Verdict.Policy.PolicyTask` in place of Verus's
  `InternalTask`.

Upstream: `verdict/src/policy/firefox.rs`.
-/

namespace Verdict.Policy

/-! ## § 1  Firefox Policy Environment -/

/-- Firefox policy environment. Similar to Chrome but with different
    trust anchors and international certificate restrictions (Tubitak,
    ANSSI).  Verus: `struct Policy` in `firefox.rs` internal module. -/
structure FirefoxPolicyEnv where
  /-- Certificate revocation list fingerprints -/
  crl : List String
  /-- Symantec root fingerprints (distrusted) -/
  symantecRoots : List String
  /-- Symantec exception fingerprints -/
  symantecExceptions : List String
  /-- Tubitak root fingerprints (restricted issuer) -/
  tubitakFingerprints : List String
  /-- Tubitak restricted domains -/
  tubitakDomains : List String
  /-- ANSSI root fingerprints (restricted issuer) -/
  anssiFingerprints : List String
  /-- ANSSI restricted domains -/
  anssiDomains : List String
  deriving Inhabited

end Verdict.Policy

/-! ## § 2  Firefox Helper Predicates (Curator-Given) -/

namespace Verdict.Policy.Firefox

open Verdict.Policy

/-- Firefox leaf EKU check. Must have serverAuth, or no EKU extension.
    Verus: `check_eku_leaf` in `firefox.rs`. -/
def checkEkuLeaf (cert : AbstractCertificate) : Bool :=
  match cert.extExtendedKeyUsage with
  | none => true
  | some eku => eku.usages.any fun u => match u with
    | .serverAuth => true
    | _ => false

/-- Firefox leaf key usage check.
    Verus: `check_key_usage_leaf` in `firefox.rs`. -/
def checkKeyUsageLeaf (cert : AbstractCertificate) : Bool :=
  match cert.extKeyUsage with
  | none => true
  | some ku => ku.digitalSignature || ku.keyEncipherment || ku.keyAgreement

/-- Firefox intermediate key usage check. Must have keyCertSign.
    Verus: `check_key_usage_intermediate` in `firefox.rs`. -/
def checkKeyUsageIntermediate (cert : AbstractCertificate) : Bool :=
  match cert.extKeyUsage with
  | none => true
  | some ku => ku.keyCertSign

/-- Strong signature — re-export of Chrome's `strongSignature`.
    Verus: `strong_signature` (firefox.rs:180). -/
def strongSignature := Verdict.Policy.Chrome.strongSignature

/-- Signature algorithm OIDs match — re-export of Chrome's `sigAlgMatch`. -/
def sigAlgMatch := Verdict.Policy.Chrome.sigAlgMatch

end Verdict.Policy.Firefox

/-! ## § 3  API Signatures (DO NOT MODIFY) -/

namespace Verdict

/-- Verify a leaf certificate under Firefox policy. The extra `ev : Bool`
    flag distinguishes Extended-Validation leaves.
    Verus: `cert_verified_leaf` (firefox.rs:574). -/
abbrev FirefoxCertVerifiedLeafSig :=
  Verdict.Policy.FirefoxPolicyEnv → Verdict.Policy.PolicyTask →
    Verdict.Policy.AbstractCertificate → Bool → Bool

/-- Verify an intermediate certificate under Firefox policy.
    Verus: `cert_verified_intermediate` (firefox.rs:566). -/
abbrev FirefoxCertVerifiedIntermediateSig :=
  Verdict.Policy.FirefoxPolicyEnv → Verdict.Policy.PolicyTask →
    Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate →
    Nat → Bool

/-- Verify a root certificate under Firefox policy. Unlike Chrome, Firefox
    passes both the last intermediate and the leaf through so Tubitak/ANSSI
    domain restrictions can be enforced against the leaf.
    Verus: `cert_verified_root` (firefox.rs:440). -/
abbrev FirefoxCertVerifiedRootSig :=
  Verdict.Policy.FirefoxPolicyEnv → Verdict.Policy.PolicyTask →
    Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate →
    Verdict.Policy.AbstractCertificate → Nat → Bool

/-- Check name constraints across the chain.
    Verus: `check_all_name_constraints` (firefox.rs:615). -/
abbrev FirefoxCheckAllNameConstraintsSig :=
  List Verdict.Policy.AbstractCertificate → Bool

/-- Firefox `likely_issued`: exact (un-normalized) DN match + AKI check.
    Verus: `likely_issued` (firefox.rs:638). -/
abbrev FirefoxLikelyIssuedSig :=
  Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate → Bool

/-- Firefox `valid_chain`: compose per-cert checks + name constraints.
    Verus: `valid_chain` (firefox.rs:625). -/
abbrev FirefoxValidChainSig :=
  Verdict.Policy.FirefoxPolicyEnv → List Verdict.Policy.AbstractCertificate →
    Verdict.Policy.PolicyTask → Bool

end Verdict

-- !benchmark @start global_aux
namespace Verdict.Policy.Firefox.Reference

def validPki (cert : AbstractCertificate) : Bool :=
  match cert.subjectKey with
  | .rsa bits => bits ≥ 2048
  | .dsa _ _ _ => false
  | .other => true

def validName (name : String) : Bool :=
  if name.any (· == '*') then
    name.length > 2 && name.startsWith "*." && !name.endsWith "." &&
      (String.ofList (name.toList.drop 2)).any (· == '.')
  else
    !name.isEmpty && !name.startsWith "." && !name.endsWith "."

def strongSignature (alg : String) : Bool :=
  ["1.2.840.10045.4.3.2", "1.2.840.10045.4.3.3", "1.2.840.10045.4.3.4",
   "1.2.840.113549.1.1.11", "1.2.840.113549.1.1.12", "1.2.840.113549.1.1.13"].contains alg

def handledExtensions (cert : AbstractCertificate) : Bool :=
  match cert.allExts with
  | none => true
  | some exts => exts.all fun ext =>
    ext.critical != some true ||
      ["2.5.29.9", "2.5.29.14", "2.5.29.15", "2.5.29.16", "2.5.29.17",
       "2.5.29.18", "2.5.29.19", "2.5.29.30", "2.5.29.31", "2.5.29.32",
       "2.5.29.33", "2.5.29.36", "2.5.29.35", "2.5.29.37",
       "1.3.6.1.5.5.7.1.1"].contains ext.oid

def subjectKeyIdNoncritical (cert : AbstractCertificate) : Bool :=
  match cert.extSubjectKeyId with
  | none => true
  | some skid => skid.critical != some true

def extendedKeyUsage (cert : AbstractCertificate) : Bool :=
  match cert.extExtendedKeyUsage with
  | none => true
  | some eku =>
    eku.usages.contains .serverAuth &&
      ((match cert.extBasicConstraints with
        | some bc => bc.isCA
        | none => false) || !eku.usages.contains .ocspSigning)

def hostnameMatches (cert : AbstractCertificate) (domain : String) : Bool :=
  match cert.extSubjectAltName with
  | some san =>
    (san.names.all fun name => match name with
      | .dnsName dns => validName dns
      | _ => true) &&
    san.names.any fun name => match name with
      | .dnsName dns => matchName (Verdict.Policy.Reference.lowerString dns)
          (Verdict.Policy.Reference.lowerString domain)
      | _ => false
  | none => cert.subject.rdns.any fun rdn => rdn.any fun attr =>
      attr.oid == "2.5.4.3" && validName attr.value &&
        matchName attr.value (Verdict.Policy.Reference.lowerString domain)

def internationalValid (env : FirefoxPolicyEnv)
    (cert leaf : AbstractCertificate) : Bool :=
  match leaf.extSubjectAltName with
  | none => true
  | some san => san.names.all fun name => match name with
    | .dnsName dns =>
      (!env.tubitakFingerprints.contains cert.fingerprint ||
        env.tubitakDomains.any (fun pattern => matchName pattern dns)) &&
      (!env.anssiFingerprints.contains cert.fingerprint ||
        env.anssiDomains.any (fun pattern => matchName pattern dns))
    | _ => true

def nonLeaf (env : FirefoxPolicyEnv) (task : PolicyTask)
    (cert leaf : AbstractCertificate) (depth : Nat) : Bool :=
  internationalValid env cert leaf && validPki cert && depth ≤ 6 &&
  (match cert.extBasicConstraints with
    | none => false
    | some bc => bc.isCA && (match bc.pathLen with
      | none => true
      | some limit => limit ≥ 0 && (depth : Int) ≤ limit)) &&
  cert.sigAlgInner.bytes == cert.sigAlgOuter.bytes &&
  cert.notBefore ≤ task.now && task.now ≤ cert.notAfter &&
  checkKeyUsageIntermediate cert &&
  (match cert.extAuthorityKeyId with
    | none => true
    | some aki => aki.critical != some true) &&
  !cert.subject.rdns.isEmpty && checkDuplicateExtensions cert &&
  handledExtensions cert && subjectKeyIdNoncritical cert

def validDnsConstraints (constraints : NameConstraints) : Bool :=
  (constraints.permitted ++ constraints.excluded).all fun name => match name with
    | .dnsName dns => !dns.isEmpty && !dns.endsWith "." && !dns.any (· == '*')
    | _ => true

def directoryConstraints (constraints : NameConstraints) (name : DistinguishedName) : Bool :=
  (!(constraints.permitted.any fun entry => match entry with
      | .directoryName _ => true
      | _ => false) ||
    constraints.permitted.any (fun entry => match entry with
      | .directoryName permitted => Verdict.Policy.Reference.isSubtreeOf permitted name false
      | _ => false)) &&
  constraints.excluded.all fun entry => match entry with
    | .directoryName excluded => !Verdict.Policy.Reference.isSubtreeOf excluded name false
    | _ => true

def dnsConstraints (constraints : NameConstraints) (name : String) : Bool :=
  (!(constraints.permitted.any fun entry => match entry with
      | .dnsName _ => true
      | _ => false) ||
    constraints.permitted.any (fun entry => match entry with
      | .dnsName permitted => permitName permitted name
      | _ => false)) &&
  constraints.excluded.all fun entry => match entry with
    | .dnsName excluded => !permitName excluded name
    | _ => true

def ipConstraints (constraints : NameConstraints) (addr : ByteArray) : Bool :=
  (!(constraints.permitted.any fun entry => match entry with
      | .ipAddr _ => true
      | _ => false) ||
    constraints.permitted.any (fun entry => match entry with
      | .ipAddr permitted => Verdict.Policy.Reference.ipAddrInRange permitted addr
      | _ => false)) &&
  constraints.excluded.all fun entry => match entry with
    | .ipAddr excluded => !Verdict.Policy.Reference.ipAddrInRange excluded addr
    | _ => true

def nameConstraints (parent target : AbstractCertificate) (isLeaf : Bool) : Bool :=
  match parent.extNameConstraints with
  | none => true
  | some constraints =>
    validDnsConstraints constraints &&
    (!constraints.permitted.isEmpty || !constraints.excluded.isEmpty) &&
    (match target.extSubjectAltName with
      | some san => san.names.all fun name => match name with
        | .dnsName dns => dnsConstraints constraints dns
        | .directoryName dn => directoryConstraints constraints dn
        | .ipAddr addr => ipConstraints constraints addr
        | .otherName => false
        | .unsupported => true
      | none => !isLeaf || target.subject.rdns.all (fun rdn => rdn.all fun attr =>
          attr.oid != "2.5.4.3" || dnsConstraints constraints attr.value)) &&
    directoryConstraints constraints target.subject

end Verdict.Policy.Firefox.Reference
-- !benchmark @end global_aux

/-! ## § 4  Firefox Per-Certificate Verification (LLM Implements) -/

-- !benchmark @start code_aux def=firefoxCertVerifiedLeaf
-- !benchmark @end code_aux def=firefoxCertVerifiedLeaf

def Verdict.firefoxCertVerifiedLeaf : Verdict.FirefoxCertVerifiedLeafSig :=
-- !benchmark @start code def=firefoxCertVerifiedLeaf
  fun env task cert ev =>
    Verdict.Policy.Firefox.Reference.validPki cert &&
    (match task.hostname with
      | none => true
      | some domain => Verdict.Policy.Firefox.Reference.hostnameMatches cert domain) &&
    (match cert.extBasicConstraints with
      | none => true
      | some bc => !bc.isCA) &&
    (!ev || (cert.notBefore ≤ cert.notAfter && cert.notAfter - cert.notBefore < 71712000)) &&
    !env.crl.contains cert.fingerprint &&
    cert.sigAlgInner.bytes == cert.sigAlgOuter.bytes &&
    cert.notBefore ≤ task.now && task.now ≤ cert.notAfter &&
    Verdict.Policy.Firefox.Reference.strongSignature cert.sigAlgInner.id &&
    Verdict.Policy.Firefox.checkKeyUsageLeaf cert &&
    Verdict.Policy.Firefox.Reference.extendedKeyUsage cert &&
    Verdict.Policy.checkDuplicateExtensions cert &&
    Verdict.Policy.Firefox.Reference.handledExtensions cert &&
    Verdict.Policy.Firefox.Reference.subjectKeyIdNoncritical cert
-- !benchmark @end code def=firefoxCertVerifiedLeaf

-- !benchmark @start code_aux def=firefoxCertVerifiedIntermediate
-- !benchmark @end code_aux def=firefoxCertVerifiedIntermediate

def Verdict.firefoxCertVerifiedIntermediate : Verdict.FirefoxCertVerifiedIntermediateSig :=
-- !benchmark @start code def=firefoxCertVerifiedIntermediate
  fun env task cert leaf depth =>
    Verdict.Policy.Firefox.Reference.nonLeaf env task cert leaf depth &&
    !env.crl.contains cert.fingerprint &&
    Verdict.Policy.Firefox.Reference.strongSignature cert.sigAlgInner.id &&
    Verdict.Policy.Firefox.Reference.extendedKeyUsage cert
-- !benchmark @end code def=firefoxCertVerifiedIntermediate

-- !benchmark @start code_aux def=firefoxCertVerifiedRoot
-- !benchmark @end code_aux def=firefoxCertVerifiedRoot

def Verdict.firefoxCertVerifiedRoot : Verdict.FirefoxCertVerifiedRootSig :=
-- !benchmark @start code def=firefoxCertVerifiedRoot
  fun env task cert interm leaf depth =>
    Verdict.Policy.Firefox.Reference.nonLeaf env task cert leaf depth &&
    !(env.symantecRoots.contains cert.fingerprint &&
      !env.symantecExceptions.contains interm.fingerprint && cert.notBefore < 1464739200) &&
    Verdict.Policy.Firefox.Reference.internationalValid env cert leaf
-- !benchmark @end code def=firefoxCertVerifiedRoot

-- !benchmark @start code_aux def=firefoxCheckAllNameConstraints
-- !benchmark @end code_aux def=firefoxCheckAllNameConstraints

def Verdict.firefoxCheckAllNameConstraints : Verdict.FirefoxCheckAllNameConstraintsSig :=
-- !benchmark @start code def=firefoxCheckAllNameConstraints
  fun chain =>
    !chain.isEmpty && (chain.zipIdx).all fun (parent, i) =>
      ((chain.take i).zipIdx).all fun (target, j) =>
        Verdict.Policy.Firefox.Reference.nameConstraints parent target (j == 0)
-- !benchmark @end code def=firefoxCheckAllNameConstraints

/-! ## § 5  Firefox Policy Composition (LLM Implements) -/

-- !benchmark @start code_aux def=firefoxLikelyIssued
-- !benchmark @end code_aux def=firefoxLikelyIssued

def Verdict.firefoxLikelyIssued : Verdict.FirefoxLikelyIssuedSig :=
-- !benchmark @start code def=firefoxLikelyIssued
  fun issuer subject =>
    Verdict.Policy.sameDN issuer.subject subject.issuer false &&
    Verdict.Policy.checkAuthKeyId issuer subject
-- !benchmark @end code def=firefoxLikelyIssued

-- !benchmark @start code_aux def=firefoxValidChain
-- !benchmark @end code_aux def=firefoxValidChain

def Verdict.firefoxValidChain : Verdict.FirefoxValidChainSig :=
-- !benchmark @start code def=firefoxValidChain
  fun env chain task =>
    chain.length ≥ 2 &&
    Verdict.firefoxCertVerifiedLeaf env task (chain.getD 0 default) false &&
    ((List.range (chain.length - 2)).all fun depth =>
      Verdict.firefoxCertVerifiedIntermediate env task (chain.getD (depth + 1) default)
        (chain.getD 0 default) depth) &&
    Verdict.firefoxCertVerifiedRoot env task (chain.getD (chain.length - 1) default)
      (chain.getD (chain.length - 2) default) (chain.getD 0 default) (chain.length - 2) &&
    Verdict.firefoxCheckAllNameConstraints chain
-- !benchmark @end code def=firefoxValidChain
