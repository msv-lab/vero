import Verdict.Impl.PolicyCommon

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.PolicyOpenSSL

Lean 4 port of `verdict/src/policy/openssl.rs` — the OpenSSL
X.509 path validation policy. Ports `verdict_old/Verdict/Policy/OpenSSL.lean`
into the new-format layout.

Note: OpenSSL has no policy environment — it is a **unit policy**
with fixed rules. The Verus source declares `struct Policy;` (a
unit struct) and the Lean API signatures therefore take no env
argument (unlike Chrome's `ChromePolicyEnv` or Firefox's
`FirefoxPolicyEnv`).

Shape:

* Curator-given: seven helper predicates (`checkCertKeyLevel`,
  `checkCertTime`, `checkCa`, `checkBasicConstraints`,
  `checkKeyUsage`, `checkSan`, `checkDuplicateExts`) live in
  `namespace Verdict.Policy.OpenSSL`. Each takes
  `Verdict.Policy.AbstractCertificate` (not the parser-layer
  `Verdict.Certificate`). `checkDuplicateExts` is a re-export of
  `Verdict.Policy.checkDuplicateExtensions`.
* Benchmark tasks: seven `!benchmark code` stubs
  (`opensslValidLeaf`, `opensslValidIntermediate`, `opensslValidRoot`,
  `opensslCheckNameConstraints`, `opensslCheckHostname`,
  `opensslLikelyIssued`, `opensslValidChain`) flat-namespaced under
  `Verdict` with matching `*Sig` type abbreviations. Signatures
  use `Verdict.Policy.PolicyTask` in place of Verus's `InternalTask`.

Upstream: `verdict/src/policy/openssl.rs`.
-/

/-! ## § 1  OpenSSL Helper Predicates (Curator-Given) -/

namespace Verdict.Policy.OpenSSL

open Verdict.Policy

/-- Check certificate key security level (≥80 bits ⟹ RSA ≥ 1024).
    Verus: `check_cert_key_level` (openssl.rs:128). -/
def checkCertKeyLevel (cert : AbstractCertificate) : Bool :=
  match cert.subjectKey with
  | .rsa modLength => modLength ≥ 1024
  | _ => true

/-- Check certificate time validity against current time.
    Verus: `check_cert_time` (openssl.rs:141). -/
def checkCertTime (cert : AbstractCertificate) (now : UInt64) : Bool :=
  cert.notBefore ≤ now && cert.notAfter > now

/-- OpenSSL CA classification (0=notCA, 1=CA, 2=other).
    Verus: `check_ca` (openssl.rs:158). -/
def checkCa (cert : AbstractCertificate) : UInt32 :=
  if cert.extKeyUsage.any (fun ku => !ku.keyCertSign) then 0
  else if cert.extBasicConstraints.any (fun bc => bc.isCA) then 1
  else if cert.extBasicConstraints.any (fun bc => !bc.isCA) then 0
  else if cert.version == 1 || cert.extKeyUsage.isSome then 2
  else 0

/-- Check basic constraints validity.
    Verus: `check_basic_constraints` (openssl.rs:174). -/
def checkBasicConstraints (cert : AbstractCertificate) : Bool :=
  match cert.extBasicConstraints with
  | none => true
  | some bc =>
    (match bc.pathLen with
     | some _ => bc.isCA && cert.extKeyUsage.any (fun ku => ku.keyCertSign)
     | none => true) &&
    (if bc.isCA then bc.critical == some true else true)

/-- Check key usage for CA vs end-entity.
    Verus: `check_key_usage` (openssl.rs:187). -/
def checkKeyUsage (cert : AbstractCertificate) : Bool :=
  match cert.extBasicConstraints with
  | some bc =>
    if bc.isCA then cert.extKeyUsage.isSome
    else match cert.extKeyUsage with
         | some ku => !ku.keyCertSign
         | none => true
  | none => match cert.extKeyUsage with
            | some ku => !ku.keyCertSign
            | none => true

/-- Check SAN is non-empty if present.
    Verus: `check_san` (openssl.rs:197). -/
def checkSan (cert : AbstractCertificate) : Bool :=
  match cert.extSubjectAltName with
  | none => true
  | some san => san.names.length > 0

/-- No duplicate extension OIDs — alias for `Verdict.Policy.checkDuplicateExtensions`. -/
def checkDuplicateExts := Verdict.Policy.checkDuplicateExtensions

end Verdict.Policy.OpenSSL

/-! ## § 2  API Signatures (DO NOT MODIFY) -/

namespace Verdict

/-- Verify a leaf certificate under OpenSSL policy.
    Verus: `valid_leaf` (openssl.rs ~350). -/
abbrev OpensslValidLeafSig :=
  Verdict.Policy.PolicyTask → Verdict.Policy.AbstractCertificate → Bool

/-- Verify an intermediate certificate under OpenSSL policy.
    Verus: `valid_intermediate` (openssl.rs ~380). -/
abbrev OpensslValidIntermediateSig :=
  Verdict.Policy.PolicyTask → Verdict.Policy.AbstractCertificate → Nat → Bool

/-- Verify a root certificate under OpenSSL policy.
    Verus: `valid_root` (openssl.rs ~410). -/
abbrev OpensslValidRootSig :=
  Verdict.Policy.PolicyTask → Verdict.Policy.AbstractCertificate → Nat → Bool

/-- Check name constraints across the OpenSSL chain.
    Verus: `check_name_constraints` in `openssl.rs`. -/
abbrev OpensslCheckNameConstraintsSig :=
  List Verdict.Policy.AbstractCertificate → Bool

/-- Check hostname against leaf certificate SAN.
    Verus: `check_hostname` (openssl.rs ~470). -/
abbrev OpensslCheckHostnameSig :=
  Verdict.Policy.AbstractCertificate → String → Bool

/-- OpenSSL `likely_issued`: DN match (normalized) + AKI check.
    Verus: `likely_issued` (openssl.rs:540). -/
abbrev OpensslLikelyIssuedSig :=
  Verdict.Policy.AbstractCertificate → Verdict.Policy.AbstractCertificate → Bool

/-- OpenSSL `valid_chain`: compose per-cert checks, name constraints,
    and hostname matching.
    Verus: `valid_chain` (openssl.rs:529). -/
abbrev OpensslValidChainSig :=
  List Verdict.Policy.AbstractCertificate → Verdict.Policy.PolicyTask → Bool

end Verdict

-- !benchmark @start global_aux
namespace Verdict.Policy.OpenSSL

def checkAuthSubjectKeyId (cert : AbstractCertificate) (isRoot isLeaf : Bool) : Bool :=
  !cert.extAuthorityKeyId.any (fun aki => aki.critical == some true) &&
  !cert.extSubjectKeyId.any (fun ski => ski.critical == some true) &&
  if cert.version >= 2 then
    (isRoot || cert.extAuthorityKeyId.any (fun aki => aki.keyId.isSome)) &&
    (isLeaf || cert.extSubjectKeyId.isSome)
  else
    cert.allExts.isNone && cert.extAuthorityKeyId.isNone &&
    cert.extSubjectKeyId.isNone && cert.extExtendedKeyUsage.isNone &&
    cert.extBasicConstraints.isNone && cert.extKeyUsage.isNone &&
    cert.extSubjectAltName.isNone && cert.extNameConstraints.isNone &&
    cert.extCertPolicies.isNone && cert.extAuthorityInfoAccess.isNone

def checkPurpose (cert : AbstractCertificate) (isLeaf : Bool) : Bool :=
  (match cert.extExtendedKeyUsage with
   | none => true
   | some eku => eku.usages.contains .serverAuth) &&
  if isLeaf then
    match cert.extKeyUsage with
    | none => true
    | some ku => ku.digitalSignature || ku.keyEncipherment || ku.keyAgreement
  else checkCa cert == 1

def checkUnhandledExtensions (cert : AbstractCertificate) : Bool :=
  match cert.allExts with
  | none => true
  | some exts => exts.all fun ext =>
    ext.critical != some true ||
      ["2.16.840.1.113730.1.1", "2.5.29.15", "2.5.29.17", "2.5.29.19",
       "2.5.29.32", "2.5.29.31", "2.5.29.37", "1.3.6.1.5.5.7.48.1.5",
       "2.5.29.36", "1.3.6.1.5.5.7.1.14", "2.5.29.30", "2.5.29.33",
       "2.5.29.54"].contains ext.oid

def validCertCommon (task : PolicyTask) (cert : AbstractCertificate)
    (isLeaf isRoot : Bool) (depth : Nat) : Bool :=
  checkCertKeyLevel cert && checkCertTime cert task.now &&
  checkBasicConstraints cert && checkKeyUsage cert &&
  (if isLeaf then checkCa cert != 2 else checkCa cert == 1) &&
  !cert.issuer.rdns.isEmpty &&
  (!cert.subject.rdns.isEmpty ||
    (cert.extSubjectAltName.any (fun san => !san.names.isEmpty && san.critical == some true) &&
     !cert.extBasicConstraints.any (fun bc => bc.isCA) &&
     !cert.extKeyUsage.any (fun ku => ku.keyCertSign))) &&
  checkSan cert && cert.sigAlgInner.bytes == cert.sigAlgOuter.bytes &&
  checkPurpose cert isLeaf && checkAuthSubjectKeyId cert isRoot isLeaf &&
  (match cert.extBasicConstraints with
   | none => true
   | some bc => match bc.pathLen with
     | none => true
     | some pathLen => pathLen >= 0 && (isLeaf || (depth : Int) <= pathLen)) &&
  checkUnhandledExtensions cert && checkDuplicateExts cert

def matchDnsName (pattern name : String) : Bool :=
  pattern.isEmpty ||
  (name.length > pattern.length &&
    (name.toList.getD (name.length - pattern.length - 1) ' ' == '.' ||
     pattern.startsWith ".") &&
    String.ofList (name.toList.drop (name.length - pattern.length)) == pattern) ||
  (name.length == pattern.length &&
    Verdict.Policy.Reference.lowerString pattern == Verdict.Policy.Reference.lowerString name)

def isGeneralSubtreeOf (constraint name : GeneralName) : Bool :=
  match constraint, name with
  | .dnsName pattern, .dnsName name => matchDnsName pattern name
  | .directoryName constraint, .directoryName name =>
    Verdict.Policy.Reference.isSubtreeOf constraint name true
  | .ipAddr range, .ipAddr addr => Verdict.Policy.Reference.ipAddrInRange range addr
  | _, _ => false

def sameGeneralNameType (a b : GeneralName) : Bool :=
  match a, b with
  | .dnsName _, .dnsName _ => true
  | .directoryName _, .directoryName _ => true
  | .ipAddr _, .ipAddr _ => true
  | _, _ => false

def ncMatch (name : GeneralName) (nc : NameConstraints) : Bool :=
  (match name with | .otherName => false | _ => true) &&
  (!nc.permitted.any (sameGeneralNameType name) ||
    nc.permitted.any (fun constraint => isGeneralSubtreeOf constraint name)) &&
  !nc.excluded.any (fun constraint => isGeneralSubtreeOf constraint name)

def checkSanHasDns (cert : AbstractCertificate) : Bool :=
  cert.extSubjectAltName.any fun san =>
    san.names.any fun name => match name with | .dnsName _ => true | _ => false

-- The source's resource limit saturates sums at the 64-bit usize maximum.
def addUsize (a b : Nat) : Nat := min (a + b) 18446744073709551615

def checkNameConstraintsHelper (cert : AbstractCertificate)
    (nc : NameConstraints) (isLeaf : Bool) : Bool :=
  let sanCount := match cert.extSubjectAltName with
    | none => 0
    | some san => san.names.length
  let nameCount := addUsize cert.subject.rdns.length sanCount
  let constraintCount := addUsize nc.permitted.length nc.excluded.length
  (nameCount == 0 || constraintCount <= 1048576 / nameCount) &&
  ncMatch (.directoryName cert.subject) nc &&
  (match cert.extSubjectAltName with
   | none => true
   | some san => san.names.all (fun name => ncMatch name nc)) &&
  (!isLeaf || checkSanHasDns cert ||
    cert.subject.rdns.all (fun rdn => rdn.all (fun attr =>
      attr.oid != "2.5.4.3" || ncMatch (.dnsName attr.value) nc)))

def checkValidPattern (pattern : String) : Bool :=
  !pattern.startsWith "*." ||
    (pattern.length >= 2 && (String.ofList (pattern.toList.drop 2)).any (· == '.'))

end Verdict.Policy.OpenSSL
-- !benchmark @end global_aux

/-! ## § 3  OpenSSL Per-Certificate Verification (LLM Implements) -/

-- !benchmark @start code_aux def=opensslValidLeaf
-- !benchmark @end code_aux def=opensslValidLeaf

def Verdict.opensslValidLeaf : Verdict.OpensslValidLeafSig :=
-- !benchmark @start code def=opensslValidLeaf
  fun task cert => Verdict.Policy.OpenSSL.validCertCommon task cert true false 0
-- !benchmark @end code def=opensslValidLeaf

-- !benchmark @start code_aux def=opensslValidIntermediate
-- !benchmark @end code_aux def=opensslValidIntermediate

def Verdict.opensslValidIntermediate : Verdict.OpensslValidIntermediateSig :=
-- !benchmark @start code def=opensslValidIntermediate
  fun task cert depth => Verdict.Policy.OpenSSL.validCertCommon task cert false false depth
-- !benchmark @end code def=opensslValidIntermediate

-- !benchmark @start code_aux def=opensslValidRoot
-- !benchmark @end code_aux def=opensslValidRoot

def Verdict.opensslValidRoot : Verdict.OpensslValidRootSig :=
-- !benchmark @start code def=opensslValidRoot
  fun task cert depth => Verdict.Policy.OpenSSL.validCertCommon task cert false true depth
-- !benchmark @end code def=opensslValidRoot

-- !benchmark @start code_aux def=opensslCheckNameConstraints
-- !benchmark @end code_aux def=opensslCheckNameConstraints

def Verdict.opensslCheckNameConstraints : Verdict.OpensslCheckNameConstraintsSig :=
-- !benchmark @start code def=opensslCheckNameConstraints
  fun chain =>
    (List.range chain.length).all fun i =>
      i == 0 || match chain[i]!.extNameConstraints with
      | none => true
      | some nc => (List.range i).all fun j =>
        Verdict.Policy.Reference.sameDN chain[j]!.subject chain[j]!.issuer true ||
        Verdict.Policy.OpenSSL.checkNameConstraintsHelper chain[j]! nc (j == 0)
-- !benchmark @end code def=opensslCheckNameConstraints

-- !benchmark @start code_aux def=opensslCheckHostname
-- !benchmark @end code_aux def=opensslCheckHostname

def Verdict.opensslCheckHostname : Verdict.OpensslCheckHostnameSig :=
-- !benchmark @start code def=opensslCheckHostname
  fun cert hostname =>
    let hostname := Verdict.Policy.Reference.lowerString hostname
    cert.extSubjectAltName.any (fun san => san.names.any (fun name =>
      match name with
      | .dnsName dnsName =>
        Verdict.Policy.OpenSSL.checkValidPattern dnsName &&
        Verdict.Policy.matchName (Verdict.Policy.Reference.lowerString dnsName) hostname
      | _ => false)) ||
    (!Verdict.Policy.OpenSSL.checkSanHasDns cert &&
      cert.subject.rdns.any (fun rdn => rdn.any (fun attr =>
        attr.oid == "2.5.4.3" && Verdict.Policy.OpenSSL.checkValidPattern attr.value &&
        Verdict.Policy.matchName (Verdict.Policy.Reference.lowerString attr.value) hostname)))
-- !benchmark @end code def=opensslCheckHostname

/-! ## § 4  OpenSSL Policy Composition (LLM Implements) -/

-- !benchmark @start code_aux def=opensslLikelyIssued
-- !benchmark @end code_aux def=opensslLikelyIssued

def Verdict.opensslLikelyIssued : Verdict.OpensslLikelyIssuedSig :=
-- !benchmark @start code def=opensslLikelyIssued
  fun issuer subject =>
    Verdict.Policy.Reference.sameDN issuer.subject subject.issuer true &&
    Verdict.Policy.checkAuthKeyId issuer subject
-- !benchmark @end code def=opensslLikelyIssued

-- !benchmark @start code_aux def=opensslValidChain
-- !benchmark @end code_aux def=opensslValidChain

def Verdict.opensslValidChain : Verdict.OpensslValidChainSig :=
-- !benchmark @start code def=opensslValidChain
  fun chain task =>
    chain.length >= 2 &&
    Verdict.opensslValidLeaf task chain[0]! &&
    ((List.range (chain.length - 2)).all fun offset =>
      Verdict.opensslValidIntermediate task chain[offset + 1]! offset) &&
    Verdict.opensslValidRoot task chain[chain.length - 1]! (chain.length - 2) &&
    Verdict.opensslCheckNameConstraints chain &&
    (match task.hostname with
     | none => true
     | some hostname => Verdict.opensslCheckHostname chain[0]! hostname)
-- !benchmark @end code def=opensslValidChain
