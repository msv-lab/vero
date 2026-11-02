import Verdict.Impl.PolicyCommon

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.PolicyChrome

Lean 4 port of `verdict/src/policy/chrome.rs` — the Chrome
certificate-transparency and validation policy. Ports
`verdict_old/Verdict/Policy/Chrome.lean` into the new-format layout.

Shape:

* Curator-given: `ChromePolicyEnv` struct and the eight helper
  predicates (`isValidPki`, `isKnownRoot`, `leafDurationValid`,
  `notInCrl`, `strongSignature`, `keyUsageValid`,
  `extendedKeyUsageValid`, `sigAlgMatch`) live in
  `namespace Verdict.Policy.Chrome`. Each takes
  `Verdict.Policy.AbstractCertificate` (not the parser-layer
  `Verdict.Certificate`).
* Benchmark tasks: six `!benchmark code` stubs
  (`chromeCertVerifiedLeaf`, `chromeCertVerifiedIntermediate`,
  `chromeCertVerifiedRoot`, `chromeCheckAllNameConstraints`,
  `chromeLikelyIssued`, `chromeValidChain`) flat-namespaced under
  `Verdict` with matching `*Sig` type abbreviations. Signatures
  use `Verdict.Policy.PolicyTask` in place of Verus's
  `InternalTask`.

Upstream: `verdict/src/policy/chrome.rs`.
-/

namespace Verdict.Policy

/-! ## § 1  Chrome Policy Environment -/

/-- Chrome policy environment carrying root fingerprints and CRL data.
    Verus: `struct Policy` in `chrome.rs` internal module. -/
structure ChromePolicyEnv where
  /-- Public suffix list entries -/
  publicSuffix : List String
  /-- Certificate revocation list fingerprints -/
  crl : List String
  /-- Known root certificate fingerprints -/
  knownRoots : List String
  /-- Symantec root fingerprints (distrusted) -/
  symantecRoots : List String
  /-- Symantec exception fingerprints -/
  symantecExceptions : List String
  /-- India CCA trusted root fingerprints -/
  indiaTrusted : List String
  /-- India CCA restricted domains -/
  indiaDomains : List String
  /-- ANSSI trusted root fingerprints -/
  anssiTrusted : List String
  /-- ANSSI restricted domains -/
  anssiDomains : List String
  deriving Inhabited

end Verdict.Policy

/-! ## § 2  Chrome Helper Predicates (Curator-Given) -/

namespace Verdict.Policy.Chrome

open Verdict.Policy

/-- Valid PKI key type. Verus: `is_valid_pki` (chrome.rs:163). -/
def isValidPki (cert : AbstractCertificate) : Bool :=
  match cert.subjectKey with
  | .rsa modLength => modLength ≥ 1024
  | .dsa _ _ _ => false
  | .other => true

/-- Certificate fingerprint is in known roots list.
    Verus: `is_known_root` (chrome.rs:172). -/
def isKnownRoot (env : ChromePolicyEnv) (root : AbstractCertificate) : Bool :=
  env.knownRoots.any (· == root.fingerprint)

/-- Leaf certificate duration validity (tiered by issuance date).
    Verus: `leaf_duration_valid` (chrome.rs:178). -/
def leafDurationValid (cert : AbstractCertificate) : Bool :=
  cert.notBefore ≤ cert.notAfter && (
    let duration := cert.notAfter - cert.notBefore
    let july2012 : UInt64 := 1341100800
    let april2015 : UInt64 := 1427846400
    let march2018 : UInt64 := 1519862400
    let july2019 : UInt64 := 1561939200
    let sep2020 : UInt64 := 1598918400
    let tenYears : UInt64 := 315532800
    let sixtyMonths : UInt64 := 157852800
    let thirtyNineMonths : UInt64 := 102643200
    let eightTwentyFiveDays : UInt64 := 71280000
    let threeNinetyEightDays : UInt64 := 34387200
    (cert.notBefore < july2012 && cert.notAfter < july2019 && duration ≤ tenYears) ||
    (cert.notBefore ≥ july2012 && cert.notBefore < april2015 && duration ≤ sixtyMonths) ||
    (cert.notBefore ≥ april2015 && cert.notBefore < march2018 && duration ≤ thirtyNineMonths) ||
    (cert.notBefore ≥ march2018 && cert.notBefore < sep2020 && duration ≤ eightTwentyFiveDays) ||
    (cert.notBefore ≥ sep2020 && duration ≤ threeNinetyEightDays))

/-- Certificate not in CRL. Verus: `not_in_crl` (chrome.rs:202). -/
def notInCrl (env : ChromePolicyEnv) (cert : AbstractCertificate) : Bool :=
  env.crl.all (· != cert.fingerprint)

/-- Signature uses a strong algorithm (SHA-256+).
    Verus: `strong_signature` (chrome.rs:206). -/
def strongSignature (alg : String) : Bool :=
  alg == "1.2.840.10045.4.3.2" ||  -- ECDSA+SHA256
  alg == "1.2.840.10045.4.3.3" ||  -- ECDSA+SHA384
  alg == "1.2.840.10045.4.3.4" ||  -- ECDSA+SHA512
  alg == "1.2.840.113549.1.1.11" || -- RSA+SHA256
  alg == "1.2.840.113549.1.1.12" || -- RSA+SHA384
  alg == "1.2.840.113549.1.1.13" || -- RSA+SHA512
  alg == "1.2.840.113549.1.1.10"    -- RSA-PSS+SHA256

/-- Key usage valid per Chrome rules. Verus: `key_usage_valid` (chrome.rs:223). -/
def keyUsageValid (cert : AbstractCertificate) : Bool :=
  match cert.extKeyUsage with
  | none => true
  | some ku =>
    match cert.extBasicConstraints with
    | some bc => if bc.isCA then ku.keyCertSign
                 else !ku.keyCertSign && (ku.digitalSignature || ku.keyEncipherment || ku.keyAgreement)
    | none => !ku.keyCertSign && (ku.digitalSignature || ku.keyEncipherment || ku.keyAgreement)

/-- Extended key usage includes serverAuth or any.
    Verus: `extended_key_usage_valid` (chrome.rs:237). -/
def extendedKeyUsageValid (cert : AbstractCertificate) : Bool :=
  match cert.extExtendedKeyUsage with
  | none => true
  | some eku => eku.usages.any fun u => match u with
    | .serverAuth => true
    | .any => true
    | _ => false

/-- Inner/outer signature algorithm OIDs match.
    Verus: checked in `cert_verified_*`. -/
def sigAlgMatch (cert : AbstractCertificate) : Bool :=
  cert.sigAlgOuter.id == cert.sigAlgInner.id

end Verdict.Policy.Chrome

/-! ## § 3  API Signatures (DO NOT MODIFY) -/

namespace Verdict

/-- Verify a leaf certificate under Chrome policy.
    Verus: `cert_verified_leaf` (chrome.rs ~350-400). -/
abbrev ChromeCertVerifiedLeafSig :=
  Verdict.Policy.ChromePolicyEnv → Verdict.Policy.PolicyTask →
    Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate → Bool

/-- Verify an intermediate certificate under Chrome policy.
    Verus: `cert_verified_intermediate` (chrome.rs ~400-450). -/
abbrev ChromeCertVerifiedIntermediateSig :=
  Verdict.Policy.ChromePolicyEnv → Verdict.Policy.PolicyTask →
    Verdict.Policy.AbstractCertificate → Nat → Bool

/-- Verify a root certificate under Chrome policy.
    Verus: `cert_verified_root` (chrome.rs ~450-500). -/
abbrev ChromeCertVerifiedRootSig :=
  Verdict.Policy.ChromePolicyEnv → Verdict.Policy.PolicyTask →
    Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate → Nat → Bool

/-- Check name constraints across the chain.
    Verus: `check_all_name_constraints` (chrome.rs:571). -/
abbrev ChromeCheckAllNameConstraintsSig :=
  List Verdict.Policy.AbstractCertificate → Bool

/-- Chrome `likely_issued`: DN match only, no AKI check.
    Verus: `likely_issued` (chrome.rs:595). -/
abbrev ChromeLikelyIssuedSig :=
  Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate → Bool

/-- Chrome `valid_chain`: compose per-cert checks + name constraints.
    Verus: `valid_chain` (chrome.rs:582). -/
abbrev ChromeValidChainSig :=
  Verdict.Policy.ChromePolicyEnv → List Verdict.Policy.AbstractCertificate →
    Verdict.Policy.PolicyTask → Bool

end Verdict

-- !benchmark @start global_aux
namespace Verdict.Policy.Chrome.Reference

open Verdict.Policy

def cleanName (name : String) : String :=
  let lower := Verdict.Policy.Reference.lowerString name
  if lower.endsWith "." && !lower.isEmpty then
    String.ofList (lower.toList.take (lower.length - 1))
  else lower

def validName (name : String) : Bool :=
  if name.contains '*' then
    name.length > 2 && name.startsWith "*." && !name.endsWith "." &&
      (String.ofList (name.toList.drop 2)).contains '.'
  else !name.isEmpty && !name.endsWith "."

def matchSanDomain (env : ChromePolicyEnv) (cert : AbstractCertificate)
    (domain : String) : Bool :=
  match cert.extSubjectAltName with
  | none => false
  | some san =>
    !san.names.isEmpty &&
    san.names.all (fun name => match name with
      | .dnsName dns => validName (cleanName dns)
      | _ => true) &&
    san.names.any (fun name => match name with
      | .dnsName dns =>
        if env.publicSuffix.any (fun suffix => matchName suffix domain) then
          cleanName dns == domain
        else matchName (cleanName dns) domain
      | _ => false)

def checkExtCritical (cert : AbstractCertificate) : Bool :=
  match cert.allExts with
  | none => true
  | some exts => exts.all (fun ext => ext.critical != some false)

def checkUnhandledExtensions (cert : AbstractCertificate) : Bool :=
  match cert.allExts with
  | none => true
  | some exts => exts.all fun ext =>
    ext.critical != some true ||
      ["2.5.29.19", "2.5.29.15", "2.5.29.37", "2.5.29.30", "2.5.29.17",
       "2.5.29.32", "2.5.29.33", "2.5.29.36", "2.5.29.54"].contains ext.oid

def checkAia (cert : AbstractCertificate) : Bool :=
  match cert.extAuthorityInfoAccess with
  | none => true
  | some aia => aia.critical != some true

def checkUidVersion (cert : AbstractCertificate) : Bool :=
  (!cert.issuerUid.isSome && !cert.subjectUid.isSome) ||
    cert.version == 2 || cert.version == 3

def nonnegativePathLen (cert : AbstractCertificate) : Bool :=
  match cert.extBasicConstraints with
  | none => true
  | some bc => match bc.pathLen with
    | none => true
    | some limit => limit ≥ 0

def certVerifiedNonLeaf (cert : AbstractCertificate) (depth : Nat) : Bool :=
  cert.version == 2 && isValidPki cert && checkExtCritical cert &&
    checkDuplicateExtensions cert && cert.sigAlgInner.bytes == cert.sigAlgOuter.bytes &&
    (match cert.extBasicConstraints with
      | none => true
      | some bc => match bc.pathLen with
        | none => true
        | some limit => limit ≥ 0 && depth ≤ limit.toNat) &&
    !cert.subject.rdns.isEmpty && checkUidVersion cert

def validDnsNameConstraints (constraints : NameConstraints) : Bool :=
  let valid := fun name => match name with
    | GeneralName.dnsName dns =>
      let name := cleanName dns
      !name.isEmpty && !name.endsWith "." && !name.contains '*'
    | _ => true
  constraints.permitted.all valid && constraints.excluded.all valid

def checkDnsNameConstraints (constraints : NameConstraints) (name : String) : Bool :=
  let name := cleanName name
  (!(constraints.permitted.any (fun entry => match entry with
      | .dnsName _ => true
      | _ => false)) ||
    constraints.permitted.any (fun entry => match entry with
      | .dnsName permitted => permitName permitted name
      | _ => false)) &&
    constraints.excluded.all (fun entry => match entry with
      | .dnsName excluded => !permitName excluded name
      | _ => true)

def checkIpNameConstraints (constraints : NameConstraints) (addr : ByteArray) : Bool :=
  (!(constraints.permitted.any (fun entry => match entry with
      | .ipAddr _ => true
      | _ => false)) ||
    constraints.permitted.any (fun entry => match entry with
      | .ipAddr permitted => Verdict.Policy.Reference.ipAddrInRange permitted addr
      | _ => false)) &&
    constraints.excluded.all (fun entry => match entry with
      | .ipAddr excluded => !Verdict.Policy.Reference.ipAddrInRange excluded addr
      | _ => true)

def checkDirectoryNameConstraints (constraints : NameConstraints)
    (name : DistinguishedName) : Bool :=
  (!(constraints.permitted.any (fun entry => match entry with
      | .directoryName _ => true
      | _ => false)) ||
    constraints.permitted.any (fun entry => match entry with
      | .directoryName permitted => Verdict.Policy.Reference.isSubtreeOf permitted name true
      | _ => false)) &&
    constraints.excluded.all (fun entry => match entry with
      | .directoryName excluded => !Verdict.Policy.Reference.isSubtreeOf excluded name true
      | _ => true)

def checkNameConstraints (cert target : AbstractCertificate) : Bool :=
  match cert.extNameConstraints with
  | none => true
  | some constraints =>
    validDnsNameConstraints constraints &&
    (!constraints.permitted.isEmpty || !constraints.excluded.isEmpty) &&
    (match target.extSubjectAltName with
      | none => true
      | some san => san.names.all fun entry => match entry with
        | .dnsName dns => checkDnsNameConstraints constraints (cleanName dns)
        | .directoryName dn => checkDirectoryNameConstraints constraints dn
        | .ipAddr addr => checkIpNameConstraints constraints addr
        | .otherName => false
        | .unsupported => true) &&
    checkDirectoryNameConstraints constraints target.subject

def validRootFingerprint (env : ChromePolicyEnv) (task : PolicyTask)
    (cert : AbstractCertificate) : Bool :=
  match task.hostname with
  | none => true
  | some domain =>
    let domain := Verdict.Policy.Reference.lowerString domain
    (!env.indiaTrusted.contains cert.fingerprint ||
      env.indiaDomains.any (fun pattern => matchName pattern domain)) &&
    (!env.anssiTrusted.contains cert.fingerprint ||
      env.anssiDomains.any (fun pattern => matchName pattern domain))

end Verdict.Policy.Chrome.Reference
-- !benchmark @end global_aux

/-! ## § 4  Chrome Per-Certificate Verification (LLM Implements) -/

-- !benchmark @start code_aux def=chromeCertVerifiedLeaf
-- !benchmark @end code_aux def=chromeCertVerifiedLeaf

def Verdict.chromeCertVerifiedLeaf : Verdict.ChromeCertVerifiedLeafSig :=
-- !benchmark @start code def=chromeCertVerifiedLeaf
  fun env task cert root =>
    cert.version == 2 && Verdict.Policy.Chrome.isValidPki cert &&
    cert.sigAlgInner.bytes == cert.sigAlgOuter.bytes &&
    cert.notBefore ≤ task.now && cert.notAfter ≥ task.now &&
    (match task.hostname with
      | none => true
      | some domain => Verdict.Policy.Chrome.Reference.matchSanDomain env cert
          (Verdict.Policy.Reference.lowerString domain)) &&
    Verdict.Policy.checkDuplicateExtensions cert && Verdict.Policy.Chrome.Reference.checkAia cert &&
    (!Verdict.Policy.Chrome.isKnownRoot env root || Verdict.Policy.Chrome.leafDurationValid cert) &&
    (!cert.subject.rdns.isEmpty ||
      (match cert.extSubjectAltName with
        | none => false
        | some san => san.critical == some true)) &&
    Verdict.Policy.Chrome.notInCrl env cert && Verdict.Policy.Chrome.strongSignature cert.sigAlgInner.id &&
    Verdict.Policy.Chrome.keyUsageValid cert && Verdict.Policy.Chrome.extendedKeyUsageValid cert &&
    Verdict.Policy.Chrome.Reference.checkExtCritical cert && Verdict.Policy.Chrome.Reference.checkUnhandledExtensions cert &&
    Verdict.Policy.Chrome.Reference.nonnegativePathLen cert && Verdict.Policy.Chrome.Reference.checkUidVersion cert
-- !benchmark @end code def=chromeCertVerifiedLeaf

-- !benchmark @start code_aux def=chromeCertVerifiedIntermediate
-- !benchmark @end code_aux def=chromeCertVerifiedIntermediate

def Verdict.chromeCertVerifiedIntermediate : Verdict.ChromeCertVerifiedIntermediateSig :=
-- !benchmark @start code def=chromeCertVerifiedIntermediate
  fun env task cert depth =>
    Verdict.Policy.Chrome.Reference.certVerifiedNonLeaf cert depth &&
    (match cert.extBasicConstraints with
      | none => false
      | some bc => bc.isCA) &&
    cert.notBefore ≤ task.now && cert.notAfter ≥ task.now && Verdict.Policy.Chrome.Reference.checkAia cert &&
    Verdict.Policy.Chrome.notInCrl env cert && Verdict.Policy.Chrome.strongSignature cert.sigAlgInner.id &&
    Verdict.Policy.Chrome.keyUsageValid cert && Verdict.Policy.Chrome.extendedKeyUsageValid cert && Verdict.Policy.Chrome.Reference.checkUnhandledExtensions cert
-- !benchmark @end code def=chromeCertVerifiedIntermediate

-- !benchmark @start code_aux def=chromeCertVerifiedRoot
-- !benchmark @end code_aux def=chromeCertVerifiedRoot

def Verdict.chromeCertVerifiedRoot : Verdict.ChromeCertVerifiedRootSig :=
-- !benchmark @start code def=chromeCertVerifiedRoot
  fun env task cert interm depth =>
    Verdict.Policy.Chrome.Reference.certVerifiedNonLeaf cert depth &&
    (match cert.extKeyUsage with
      | none => true
      | some ku => ku.keyCertSign) &&
    (match cert.extAuthorityKeyId with
      | none => true
      | some aki => aki.issuer.isNone == aki.serial.isNone) &&
    Verdict.Policy.Chrome.Reference.validRootFingerprint env task cert &&
    (!env.symantecRoots.contains cert.fingerprint ||
      env.symantecExceptions.contains interm.fingerprint)
-- !benchmark @end code def=chromeCertVerifiedRoot

-- !benchmark @start code_aux def=chromeCheckAllNameConstraints
-- !benchmark @end code_aux def=chromeCheckAllNameConstraints

def Verdict.chromeCheckAllNameConstraints : Verdict.ChromeCheckAllNameConstraintsSig :=
-- !benchmark @start code def=chromeCheckAllNameConstraints
  fun chain =>
    !chain.isEmpty && (List.range (chain.length - 2)).all fun depth =>
      let i := depth + 1
      (List.range i).all fun j =>
        Verdict.Policy.Chrome.Reference.checkNameConstraints chain[i]! chain[j]!
-- !benchmark @end code def=chromeCheckAllNameConstraints

/-! ## § 5  Chrome Policy Composition (LLM Implements) -/

-- !benchmark @start code_aux def=chromeLikelyIssued
-- !benchmark @end code_aux def=chromeLikelyIssued

def Verdict.chromeLikelyIssued : Verdict.ChromeLikelyIssuedSig :=
-- !benchmark @start code def=chromeLikelyIssued
  fun issuer subject => Verdict.Policy.Reference.sameDN issuer.subject subject.issuer true
-- !benchmark @end code def=chromeLikelyIssued

-- !benchmark @start code_aux def=chromeValidChain
/-- Check every adjacent certificate pair for matching authority/subject key IDs. -/
def Verdict.chromeCheckAuthorityKeyIds (chain : List Verdict.Policy.AbstractCertificate) : Bool :=
  (List.range (chain.length - 1)).all fun i =>
    Verdict.Policy.checkAuthKeyId chain[i + 1]! chain[i]!
-- !benchmark @end code_aux def=chromeValidChain

def Verdict.chromeValidChain : Verdict.ChromeValidChainSig :=
-- !benchmark @start code def=chromeValidChain
  fun env chain task =>
    chain.length ≥ 2 &&
    Verdict.chromeCertVerifiedLeaf env task chain[0]! chain[chain.length - 1]! &&
    (List.range (chain.length - 2)).all (fun depth =>
      Verdict.chromeCertVerifiedIntermediate env task chain[depth + 1]! depth) &&
    Verdict.chromeCertVerifiedRoot env task chain[chain.length - 1]!
      chain[chain.length - 2]! (chain.length - 2) &&
    (Verdict.chromeCheckAllNameConstraints chain && Verdict.chromeCheckAuthorityKeyIds chain)
-- !benchmark @end code def=chromeValidChain
