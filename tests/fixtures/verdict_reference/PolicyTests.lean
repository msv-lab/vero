import Verdict.Impl.PolicyChrome
import Verdict.Impl.PolicyFirefox
import Verdict.Impl.PolicyOpenSSL
import Verdict.Impl.Hex

/-! Executable regressions against verdict 9bc18bc5, outside the benchmark sandbox.
These test source behavior, including intentional differences between policies.
-/
namespace Verdict.ReferencePolicyTests

open Verdict.Policy

private def dn (name : String) : DistinguishedName :=
  ⟨[[⟨"2.5.4.3", name⟩]]⟩

private def san (name : String) : Option SubjectAltName :=
  some ⟨none, [.dnsName name]⟩

private def task : PolicyTask := ⟨none, .serverAuth, 1600000001⟩
private def chrome : ChromePolicyEnv := default
private def firefox : FirefoxPolicyEnv := default

private def leaf : AbstractCertificate :=
  { (default : AbstractCertificate) with
    fingerprint := "leaf"
    version := 2
    serial := "serial"
    sigAlgInner := ⟨"1.2.840.113549.1.1.11", "same DER"⟩
    sigAlgOuter := ⟨"1.2.840.113549.1.1.11", "same DER"⟩
    notBefore := 1600000000
    notAfter := 1600000010
    issuer := dn "issuer"
    subject := dn "www.example.test"
    subjectKey := .rsa 2048
    extAuthorityKeyId := some ⟨none, some "key", none, none⟩
    extSubjectKeyId := some ⟨none, "key"⟩
    extSubjectAltName := san "www.example.test" }

private def ca (fingerprint : String) (limit : Int) : AbstractCertificate :=
  { leaf with
    fingerprint := fingerprint
    subject := dn fingerprint
    extSubjectAltName := none
    extBasicConstraints := some ⟨some true, true, some limit⟩
    extKeyUsage := some { (default : KeyUsage) with keyCertSign := true } }

private def interm := ca "intermediate" 0
private def root := ca "root" 1
private def chain := [leaf, interm, root]
private def longLeaf := { leaf with notAfter := 1634560000 }
private def excluded : Option NameConstraints :=
  some ⟨some true, [], [.dnsName "blocked.test"]⟩
private def blocked := { leaf with extSubjectAltName := san "blocked.test" }
private def constrained := { interm with extNameConstraints := excluded }

-- Results are in Chrome / Firefox / OpenSSL order; the target is not self-issued.
private def ncChecks (target : AbstractCertificate)
    (permitted excluded : List GeneralName) : List Bool :=
  let parent := { interm with extNameConstraints := some ⟨some true, permitted, excluded⟩ }
  [chromeCheckAllNameConstraints [target, parent, root],
   firefoxCheckAllNameConstraints [target, parent, root],
   opensslCheckNameConstraints [target, parent, root]]

private def dnPrefix : DistinguishedName :=
  ⟨[[⟨"2.5.4.6", "US"⟩], [⟨"2.5.4.10", "Acme"⟩]]⟩
private def dnTarget : DistinguishedName :=
  ⟨[[⟨"2.5.4.6", "US"⟩], [⟨"2.5.4.7", "Town"⟩, ⟨"2.5.4.10", "Acme"⟩],
    [⟨"2.5.4.3", "service"⟩]]⟩
private def ipTarget (addr : ByteArray) : AbstractCertificate :=
  { leaf with extSubjectAltName := some ⟨none, [.ipAddr addr]⟩ }
private def ipv4Range : ByteArray := ⟨#[192, 0, 2, 0, 255, 255, 255, 0]⟩
private def ipv6Range : ByteArray :=
  ⟨#[32, 1, 13, 184, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     255, 255, 255, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩

-- Empty/singleton chains fail validation, but constraint-checker empty behavior differs.
#guard !chromeValidChain chrome [] task && !chromeValidChain chrome [leaf] task &&
  !firefoxValidChain firefox [] task && !firefoxValidChain firefox [leaf] task &&
  !opensslValidChain [] task && !opensslValidChain [leaf] task
#guard !chromeCheckAllNameConstraints [] && chromeCheckAllNameConstraints [leaf] &&
  !firefoxCheckAllNameConstraints [] && firefoxCheckAllNameConstraints [leaf] &&
  opensslCheckNameConstraints [] && opensslCheckNameConstraints [leaf]

-- A three-certificate chain requires intermediate depth 0 and root depth 1.
#guard chromeValidChain chrome chain task && firefoxValidChain firefox chain task &&
  opensslValidChain chain task
#guard !chromeValidChain chrome [leaf, interm, ca "root" 0] task &&
  !firefoxValidChain firefox [leaf, interm, ca "root" 0] task &&
  !opensslValidChain [leaf, interm, ca "root" 0] task
#guard chromeCertVerifiedIntermediate chrome task interm 0 &&
  !chromeCertVerifiedIntermediate chrome task interm 1 &&
  firefoxCertVerifiedIntermediate firefox task interm leaf 0 &&
  !firefoxCertVerifiedIntermediate firefox task interm leaf 1 &&
  opensslValidIntermediate task interm 0 && !opensslValidIntermediate task interm 1
#guard chromeCertVerifiedRoot chrome task root interm 1 &&
  !chromeCertVerifiedRoot chrome task root interm 2 &&
  firefoxCertVerifiedRoot firefox task root interm leaf 1 &&
  !firefoxCertVerifiedRoot firefox task root interm leaf 2 &&
  opensslValidRoot task root 1 && !opensslValidRoot task root 2

-- Chrome/Firefox include notAfter; OpenSSL excludes it. All include notBefore.
#guard ([1600000000, 1600000010] : List UInt64).all (fun now =>
  chromeCertVerifiedLeaf chrome { task with now := now } leaf root &&
  firefoxCertVerifiedLeaf firefox { task with now := now } leaf false) &&
  opensslValidLeaf { task with now := 1600000000 } leaf &&
  !opensslValidLeaf { task with now := 1600000010 } leaf
#guard !chromeCertVerifiedLeaf chrome { task with now := 1599999999 } leaf root &&
  !firefoxCertVerifiedLeaf firefox { task with now := 1599999999 } leaf false &&
  !opensslValidLeaf { task with now := 1599999999 } leaf

-- Only the supplied Chrome root controls the leaf-duration restriction.
#guard chromeCertVerifiedLeaf { chrome with knownRoots := ["leaf"] } task longLeaf root &&
  !chromeCertVerifiedLeaf { chrome with knownRoots := ["root"] } task longLeaf root &&
  !chromeValidChain { chrome with knownRoots := ["root"] } [longLeaf, interm, root] task

-- Firefox's EV flag has a strict 27-month boundary; ordinary chains use false.
#guard firefoxCertVerifiedLeaf firefox task longLeaf true &&
  firefoxCertVerifiedLeaf firefox task { leaf with notAfter := 1671712000 } false &&
  !firefoxCertVerifiedLeaf firefox task { leaf with notAfter := 1671712000 } true &&
  firefoxValidChain firefox [{ leaf with notAfter := 1671712000 }, interm, root] task

-- Root distrust exceptions use the preceding certificate, not the leaf or root.
#guard chromeCertVerifiedRoot
    { chrome with symantecRoots := ["root"], symantecExceptions := ["intermediate"] }
    task root interm 1 &&
  !chromeCertVerifiedRoot
    { chrome with symantecRoots := ["root"], symantecExceptions := ["leaf"] }
    task root interm 1 &&
  chromeValidChain
    { chrome with symantecRoots := ["root"], symantecExceptions := ["intermediate"] }
    chain task &&
  !chromeValidChain
    { chrome with symantecRoots := ["root"], symantecExceptions := ["leaf"] }
    chain task
#guard firefoxCertVerifiedRoot
    { firefox with symantecRoots := ["root"], symantecExceptions := ["intermediate"] }
    task { root with notBefore := 1400000000 } interm leaf 1 &&
  !firefoxCertVerifiedRoot
    { firefox with symantecRoots := ["root"], symantecExceptions := ["leaf"] }
    task { root with notBefore := 1400000000 } interm leaf 1 &&
  firefoxValidChain
    { firefox with symantecRoots := ["root"], symantecExceptions := ["intermediate"] }
    [leaf, interm, { root with notBefore := 1400000000 }] task &&
  !firefoxValidChain
    { firefox with symantecRoots := ["root"], symantecExceptions := ["leaf"] }
    [leaf, interm, { root with notBefore := 1400000000 }] task

-- Firefox restrictions inspect the supplied leaf SAN for both non-leaf APIs.
#guard firefoxCertVerifiedIntermediate
    { firefox with tubitakFingerprints := ["intermediate"], tubitakDomains := ["*.example.test"] }
    task interm leaf 0 &&
  !firefoxCertVerifiedIntermediate
    { firefox with tubitakFingerprints := ["intermediate"], tubitakDomains := ["*.example.test"] }
    task interm blocked 0 &&
  firefoxCertVerifiedRoot
    { firefox with anssiFingerprints := ["root"], anssiDomains := ["*.example.test"] }
    task root interm leaf 1 &&
  !firefoxCertVerifiedRoot
    { firefox with anssiFingerprints := ["root"], anssiDomains := ["*.example.test"] }
    task root interm blocked 1 &&
  !firefoxValidChain
    { firefox with anssiFingerprints := ["root"], anssiDomains := ["*.example.test"] }
    [blocked, interm, root] task &&
  !firefoxValidChain
    { firefox with tubitakFingerprints := ["intermediate"], tubitakDomains := ["*.example.test"] }
    [blocked, interm, root] task

-- Chrome ignores root constraints; Firefox and OpenSSL apply them.
#guard chromeCheckAllNameConstraints [blocked, { root with extNameConstraints := excluded }] &&
  !firefoxCheckAllNameConstraints [blocked, { root with extNameConstraints := excluded }] &&
  !opensslCheckNameConstraints [blocked, { root with extNameConstraints := excluded }]
#guard chromeCheckAllNameConstraints [leaf, constrained, root] &&
  firefoxCheckAllNameConstraints [leaf, constrained, root] &&
  opensslCheckNameConstraints [leaf, constrained, root] &&
  !chromeCheckAllNameConstraints [blocked, constrained, root] &&
  !firefoxCheckAllNameConstraints [blocked, constrained, root] &&
  !opensslCheckNameConstraints [blocked, constrained, root]

-- Constraints cover non-leaf descendants too; OpenSSL skips self-issued ones.
#guard !chromeCheckAllNameConstraints
    [leaf, { blocked with issuer := blocked.subject }, constrained, root] &&
  !firefoxCheckAllNameConstraints
    [leaf, { blocked with issuer := blocked.subject }, constrained, root] &&
  opensslCheckNameConstraints
    [leaf, { blocked with issuer := blocked.subject }, constrained, root]

-- Firefox checks leaf CN only with no SAN; OpenSSL also falls back with no DNS SAN.
#guard !firefoxCheckAllNameConstraints
    [{ leaf with subject := dn "blocked.test", extSubjectAltName := none }, constrained] &&
  firefoxCheckAllNameConstraints
    [{ leaf with subject := dn "blocked.test", extSubjectAltName := some ⟨none, [.unsupported]⟩ }, constrained] &&
  !opensslCheckNameConstraints
    [{ leaf with subject := dn "blocked.test", extSubjectAltName := some ⟨none, [.unsupported]⟩ }, constrained]

-- Directory constraints use the original RDN prefix, including permitted/excluded paths.
#guard
  let constraintDn : DistinguishedName := ⟨dnTarget.rdns.take 2⟩
  ncChecks { leaf with subject := dnTarget } [.directoryName constraintDn] [] == [true, true, true] &&
  ncChecks { leaf with subject := dnTarget } [] [.directoryName constraintDn] == [false, false, false]
-- Attributes within each prefix RDN are a subset, independent of attribute order.
#guard ([dnPrefix,
    ⟨[[⟨"2.5.4.6", "US"⟩], [⟨"2.5.4.10", "Acme"⟩, ⟨"2.5.4.7", "Town"⟩]]⟩] :
    List DistinguishedName).all (fun constraintDn =>
  ncChecks { leaf with subject := dnTarget } [.directoryName constraintDn] [] == [true, true, true] &&
  ncChecks { leaf with subject := dnTarget } [] [.directoryName constraintDn] == [false, false, false])
-- Reversing the relation, or matching a later RDN instead of the prefix, fails.
#guard ([(dnPrefix, dnTarget), (dn "service", dnTarget),
    (dnTarget, dn "service")] : List (DistinguishedName × DistinguishedName)).all
    (fun (target, constraint) =>
  ncChecks { leaf with subject := target } [.directoryName constraint] [] == [false, false, false] &&
  ncChecks { leaf with subject := target } [] [.directoryName constraint] == [true, true, true])
-- Chrome/OpenSSL normalize DN values; Firefox compares the original values.
#guard ncChecks { leaf with subject := dn "service name" }
    [.directoryName (dn " SERVICE  NAME ")] [] == [true, false, true] &&
  ncChecks { leaf with subject := dn "service name" }
    [] [.directoryName (dn " SERVICE  NAME ")] == [false, true, false]

-- Non-ASCII case folding is delegated, preserving the existing opaque abstraction.
example : Verdict.Policy.Reference.lowerChar 'É' = Verdict.charLower 'É' := rfl
example : Verdict.Policy.Reference.lowerChar 'İ' = Verdict.charLower 'İ' := rfl

-- Both IP families apply the mask, accepting an in-range host and rejecting another subnet.
#guard ([((⟨#[192, 0, 2, 123]⟩ : ByteArray), true), (⟨#[192, 0, 3, 123]⟩, false)]).all
    (fun (addr, isMatch) =>
  ncChecks (ipTarget addr) [.ipAddr ipv4Range] [] == [isMatch, isMatch, isMatch] &&
  ncChecks (ipTarget addr) [] [.ipAddr ipv4Range] == [!isMatch, !isMatch, !isMatch])
#guard ([((⟨#[32, 1, 13, 184, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩ : ByteArray), true),
    (⟨#[32, 1, 13, 185, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩, false)]).all
    (fun (addr, isMatch) =>
  ncChecks (ipTarget addr) [.ipAddr ipv6Range] [] == [isMatch, isMatch, isMatch] &&
  ncChecks (ipTarget addr) [] [.ipAddr ipv6Range] == [!isMatch, !isMatch, !isMatch])
-- A 2:1 length ratio alone is insufficient: only IPv4 and IPv6 lengths are legal.
#guard ([(⟨#[]⟩, ⟨#[]⟩), (⟨#[0, 0]⟩, ⟨#[0]⟩),
    (⟨Array.replicate 34 0⟩, ⟨Array.replicate 17 0⟩)] : List (ByteArray × ByteArray)).all
    (fun (range, addr) =>
  ncChecks (ipTarget addr) [.ipAddr range] [] == [false, false, false] &&
  ncChecks (ipTarget addr) [] [.ipAddr range] == [true, true, true])
-- Malformed range sizes and cross-family pairs do not match either constraint path.
#guard ([(⟨Array.replicate 7 0⟩, ⟨Array.replicate 4 0⟩),
    (⟨Array.replicate 31 0⟩, ⟨Array.replicate 16 0⟩),
    (ipv4Range, ⟨Array.replicate 16 0⟩), (ipv6Range, ⟨Array.replicate 4 0⟩)] :
    List (ByteArray × ByteArray)).all (fun (range, addr) =>
  ncChecks (ipTarget addr) [.ipAddr range] [] == [false, false, false] &&
  ncChecks (ipTarget addr) [] [.ipAddr range] == [true, true, true])

-- SAN suppresses OpenSSL CN fallback only when it contains a DNS name.
#guard opensslCheckHostname { leaf with extSubjectAltName := none } "WWW.EXAMPLE.TEST" &&
  opensslCheckHostname { leaf with extSubjectAltName := some ⟨none, [.unsupported]⟩ } "www.example.test" &&
  !opensslCheckHostname { leaf with extSubjectAltName := san "other.test" } "www.example.test"
#guard opensslCheckHostname { leaf with extSubjectAltName := san "*.example.test" } "A.EXAMPLE.TEST" &&
  !opensslCheckHostname { leaf with extSubjectAltName := san "*.example.test" } "a.b.example.test" &&
  !opensslCheckHostname { leaf with extSubjectAltName := san "*.test" } "a.test"
#guard chromeCertVerifiedLeaf chrome { task with hostname := some "WWW.EXAMPLE.TEST" } leaf root &&
  !chromeCertVerifiedLeaf chrome { task with hostname := some "www.example.test" }
    { leaf with extSubjectAltName := none } root &&
  firefoxCertVerifiedLeaf firefox { task with hostname := some "www.example.test" }
    { leaf with extSubjectAltName := none } false &&
  !opensslValidChain chain { task with hostname := some "other.test" }

-- Issuer/subject direction, normalized DN differences, and Chrome's omitted AKI check.
#guard chromeLikelyIssued { root with subject := dn " CA " }
    { leaf with issuer := dn "ca", extAuthorityKeyId := some ⟨none, some "wrong", none, none⟩ } &&
  !firefoxLikelyIssued { root with subject := dn " CA " } { leaf with issuer := dn "ca" } &&
  opensslLikelyIssued { root with subject := dn " CA " } { leaf with issuer := dn "ca" } &&
  !opensslLikelyIssued { root with subject := dn " CA " }
    { leaf with issuer := dn "ca", extAuthorityKeyId := some ⟨none, some "wrong", none, none⟩ }
#guard firefoxLikelyIssued { root with subject := dn "issuer" } leaf &&
  !chromeLikelyIssued leaf root && !firefoxLikelyIssued leaf root && !opensslLikelyIssued leaf root

#guard toHexUpper [] == "" &&
  toHexUpper [0, 1, 15, 16, 127, 128, 171, 205, 239, 255] == "00010F107F80ABCDEFFF"

end Verdict.ReferencePolicyTests
