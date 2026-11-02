import Verdict.Impl.Asn1

-- !benchmark @start imports
-- !benchmark @end imports

/-!
# Verdict.Impl.PolicyCommon

Abstract policy-layer certificate representation + shared predicate
helpers used across Chrome / Firefox / OpenSSL and the validator's
chain-policy checks. Ported from `verdict_old/Verdict/Policy/Common.lean`
into the new-format layout.

All types + defs here are curator-given vocabulary (DO NOT MODIFY).
They are distinct from the parser-layer `Verdict.Certificate` (in
`Impl/Asn1.lean`, which mirrors Verus's `SpecCertificateValue`);
this module's `AbstractCertificate` mirrors Verus's
`policy::Certificate`.

Upstream: `verdict/src/policy/common.rs` +
`verdict/src/issue.rs` (normalize_string is aliased into
`policy/common.rs`).
-/

namespace Verdict.Policy

/-! ## § 1  String and Name Helpers -/

/-- An OID-and-value attribute in a Distinguished Name.
    Verus `rspec!`: `pub struct Attribute { pub oid: SpecString, pub value: SpecString }` -/
structure Attribute where
  oid   : String
  value : String
  deriving Repr, DecidableEq, Inhabited

/-- An X.509 Distinguished Name as an abstract sequence of RDNs,
    with attribute values decoded to strings.
    Verus `rspec!`: `pub struct DistinguishedName(pub Seq<Seq<Attribute>>)` -/
structure DistinguishedName where
  rdns : List (List Attribute)
  deriving Repr, DecidableEq, Inhabited

/-- A GeneralName as used in Subject Alternative Names and Name Constraints.
    Verus `rspec!`: `pub enum GeneralName { DNSName, DirectoryName, IPAddr, OtherName, Unsupported }` -/
inductive GeneralName where
  | dnsName       (name : String)
  | directoryName (dn   : DistinguishedName)
  | ipAddr        (addr : ByteArray)
  | otherName
  | unsupported
  deriving Inhabited

/-! ## § 2  Subject Public Key -/

/-- The type of the subject public key.
    Verus `rspec!`: `pub enum SubjectKey { RSA { mod_length }, DSA { ... }, Other }` -/
inductive SubjectKey where
  | rsa (modLength : Nat)
  | dsa (pLen qLen gLen : Nat)
  | other
  deriving Repr, DecidableEq, Inhabited

/-! ## § 3  Certificate Extensions -/

/-- RFC 5280 §4.2.1.1 Authority Key Identifier. -/
structure AuthorityKeyIdentifier where
  critical : Option Bool
  keyId    : Option String
  issuer   : Option String
  serial   : Option String
  deriving Repr, DecidableEq, Inhabited

/-- RFC 5280 §4.2.1.2 Subject Key Identifier. -/
structure SubjectKeyIdentifier where
  critical : Option Bool
  keyId    : String
  deriving Repr, DecidableEq, Inhabited

/-- Extended Key Usage purpose OIDs (RFC 5280 §4.2.1.12). -/
inductive ExtendedKeyUsageType where
  | serverAuth
  | clientAuth
  | codeSigning
  | emailProtection
  | timeStamping
  | ocspSigning
  | any
  | other (oid : String)
  deriving Repr, DecidableEq, Inhabited

/-- RFC 5280 §4.2.1.12 Extended Key Usage. -/
structure ExtendedKeyUsage where
  critical : Option Bool
  usages   : List ExtendedKeyUsageType
  deriving Repr, DecidableEq, Inhabited

/-- RFC 5280 §4.2.1.9 Basic Constraints. `isCA` is plain `Bool`
    (not `Option`) per the Verus source. -/
structure BasicConstraints where
  critical : Option Bool
  isCA     : Bool
  pathLen  : Option Int
  deriving Repr, DecidableEq, Inhabited

/-- RFC 5280 §4.2.1.3 Key Usage — all nine named bits. -/
structure KeyUsage where
  critical         : Option Bool
  digitalSignature : Bool
  nonRepudiation   : Bool
  keyEncipherment  : Bool
  dataEncipherment : Bool
  keyAgreement     : Bool
  keyCertSign      : Bool
  crlSign          : Bool
  encipherOnly     : Bool
  decipherOnly     : Bool
  deriving Repr, DecidableEq, Inhabited

/-- RFC 5280 §4.2.1.6 Subject Alternative Name. -/
structure SubjectAltName where
  critical : Option Bool
  names    : List GeneralName
  deriving Inhabited

/-- RFC 5280 §4.2.1.10 Name Constraints.
    Verus uses flat `permitted`/`excluded` sequences (not `Option`). -/
structure NameConstraints where
  critical  : Option Bool
  permitted : List GeneralName
  excluded  : List GeneralName
  deriving Inhabited

/-- RFC 5280 §4.2.1.4 Certificate Policies. -/
structure CertificatePolicies where
  critical : Option Bool
  policies : List String
  deriving Repr, DecidableEq, Inhabited

/-- RFC 5280 §4.2.2.1 Authority Information Access (presence-only). -/
structure AuthorityInfoAccess where
  critical : Option Bool
  deriving Repr, DecidableEq, Inhabited

/-- Signature algorithm OID + raw DER bytes of the AlgorithmIdentifier. -/
structure SignatureAlgorithm where
  id    : String
  bytes : String
  deriving Repr, DecidableEq, Inhabited

/-- Generic extension record (OID + criticality) for extensions not
    specifically parsed. Used in `allExts` to check duplicates. -/
structure Extension where
  oid      : String
  critical : Option Bool
  deriving Repr, DecidableEq, Inhabited

/-! ## § 4  Abstract Certificate -/

/-- The abstract policy-layer certificate. Distinct from
    `Verdict.Certificate` (parser-layer / `SpecCertificateValue`).
    Mapping provided by `Verdict.certFromParsed` (see `Impl/Convert.lean`).

    Verus `rspec!` in `policy/common.rs`: `pub struct Certificate {...}`. -/
structure AbstractCertificate where
  fingerprint            : String
  version                : UInt32
  serial                 : String
  sigAlgOuter            : SignatureAlgorithm
  sigAlgInner            : SignatureAlgorithm
  notBefore              : UInt64
  notAfter               : UInt64
  issuer                 : DistinguishedName
  subject                : DistinguishedName
  subjectKey             : SubjectKey
  issuerUid              : Option String
  subjectUid             : Option String
  extAuthorityKeyId      : Option AuthorityKeyIdentifier
  extSubjectKeyId        : Option SubjectKeyIdentifier
  extExtendedKeyUsage    : Option ExtendedKeyUsage
  extBasicConstraints    : Option BasicConstraints
  extKeyUsage            : Option KeyUsage
  extSubjectAltName      : Option SubjectAltName
  extNameConstraints     : Option NameConstraints
  extCertPolicies        : Option CertificatePolicies
  extAuthorityInfoAccess : Option AuthorityInfoAccess
  allExts                : Option (List Extension)
  deriving Inhabited

/-! ## § 5  Task and Purpose -/

/-- Validation purpose. -/
inductive Purpose where
  | serverAuth
  deriving Repr, DecidableEq, Inhabited

/-- Policy-layer validation context. Distinct from `Verdict.Task` —
    that one carries fewer fields; this one matches Verus's internal
    `InternalTask` shape. -/
structure PolicyTask where
  hostname : Option String
  purpose  : Purpose
  now      : UInt64
  deriving Inhabited

/-- Policy execution error. -/
inductive PolicyError where
  | unsupportedTask
  deriving Repr

/-! ## § 6  String Normalization -/

/-- RFC 4518 string normalization for Distinguished Name comparison.
    Verus: `pub open spec fn spec_normalize_string(s: Seq<char>) -> Seq<char>`.
    Steps: (1) case-fold to lower; (2) strip leading/trailing spaces;
    (3) collapse internal space runs. -/
def normalizeString (s : String) : String :=
  s.toLower.splitOn " " |>.filter (!·.isEmpty) |> String.intercalate " "

/-! ## § 7  Predicate API -/

/-- Two attributes are equal with optional value normalization. -/
def sameAttr (a1 a2 : Attribute) (normalize : Bool) : Bool :=
  a1.oid == a2.oid &&
  if normalize then
    a1.value == a2.value || normalizeString a1.value == normalizeString a2.value
  else
    a1.value == a2.value

/-- RDN element-wise `sameAttr`. -/
def sameRDN (rdn1 rdn2 : List Attribute) (normalize : Bool) : Bool :=
  rdn1.length == rdn2.length &&
  (rdn1.zip rdn2).all fun (a1, a2) => sameAttr a1 a2 normalize

/-- DN-wise `sameRDN`. `normalize = true` → Chrome-style;
    `false` → Firefox-style exact. -/
def sameDN (dn1 dn2 : DistinguishedName) (normalize : Bool) : Bool :=
  dn1.rdns.length == dn2.rdns.length &&
  (dn1.rdns.zip dn2.rdns).all fun (r1, r2) => sameRDN r1 r2 normalize

/-- `name1` is a suffix-subset of `name2` at the RDN level. -/
def isSubtreeOf (name1 name2 : DistinguishedName) (normalize : Bool) : Bool :=
  name2.rdns.length ≤ name1.rdns.length &&
  sameDN { rdns := name1.rdns.drop (name1.rdns.length - name2.rdns.length) } name2 normalize

/-- RFC 6125 §6.4 wildcard hostname matching. Mirrors upstream Verus
    `match_name` (verdict/src/policy/common.rs): raw string comparison, no
    `normalizeString` — the wildcard suffix is checked against `name` verbatim,
    and the non-wildcard case is exact equality. -/
def matchName (pattern name : String) : Bool :=
  if pattern.startsWith "*." then
    let nameLen := name.length
    let patLen  := pattern.length
    patLen > 2 &&
      (String.ofList (pattern.toList.drop 2) == name ||
        (nameLen > patLen - 1 &&
         name.endsWith (String.ofList (pattern.toList.drop 1)) &&
         !(String.ofList (name.toList.take (nameLen - (patLen - 1)))).any (· == '.')))
  else
    pattern == name

/-- Name Constraints permitted-subtree check for a DNS name. Mirrors upstream
    Verus `permit_name` (verdict/src/policy/common.rs): raw comparison, no
    `normalizeString`. Empty constraint matches everything; a `.`-prefixed
    constraint must be a suffix of `name`; otherwise `name` equals the
    constraint or has a `.<constraint>` suffix. -/
def permitName (nameConstraint name : String) : Bool :=
  nameConstraint.isEmpty ||
  (if nameConstraint.startsWith "." then
    nameConstraint.length ≤ name.length &&
      String.ofList (name.toList.drop (name.length - nameConstraint.length)) == nameConstraint
  else
    name == nameConstraint ||
      (name.length > nameConstraint.length &&
       (name.toList.getD (name.length - nameConstraint.length - 1) ' ') == '.' &&
       String.ofList (name.toList.drop (name.length - nameConstraint.length)) == nameConstraint))

/-- IP-address subnet range check (IPv4: 8-byte range, 4-byte addr;
    IPv6: 32-byte range, 16-byte addr). -/
def ipAddrInRange (range addr : ByteArray) : Bool :=
  let addrLen := addr.size
  range.size == 2 * addrLen &&
  (List.range addrLen).all fun i =>
    (range[i]! &&& range[i + addrLen]!) == (addr[i]! &&& range[i + addrLen]!)

/-- RFC 5280 §4.2.1.1 Authority Key Identifier check. -/
def checkAuthKeyId (issuer subject : AbstractCertificate) : Bool :=
  match subject.extAuthorityKeyId with
  | none => true
  | some aki =>
    let keyIdOk := match (issuer.extSubjectKeyId, aki.keyId) with
      | (some skid, some akid) => skid.keyId == akid
      | _                      => true
    let serialOk := match aki.serial with
      | some s => s == issuer.serial
      | none   => true
    keyIdOk && serialOk

/-- No two extensions share the same OID. -/
def checkDuplicateExtensions (cert : AbstractCertificate) : Bool :=
  match cert.allExts with
  | none => true
  | some exts =>
    let oids := exts.map Extension.oid
    oids.eraseDups.length == oids.length

/-- Certificate has a DirectoryName in its Name Constraints. -/
def hasDirectoryNameConstraint (cert : AbstractCertificate) : Bool :=
  match cert.extNameConstraints with
  | none => false
  | some nc => nc.permitted.any fun gn => match gn with
    | .directoryName _ => true
    | _ => false

/-- Certificate has a DNSName in its Name Constraints. -/
def hasDnsNameConstraint (cert : AbstractCertificate) : Bool :=
  match cert.extNameConstraints with
  | none => false
  | some nc => nc.permitted.any fun gn => match gn with
    | .dnsName _ => true
    | _ => false

/-- Certificate has an IPAddr in its Name Constraints. -/
def hasIpAddrNameConstraint (cert : AbstractCertificate) : Bool :=
  match cert.extNameConstraints with
  | none => false
  | some nc => nc.permitted.any fun gn => match gn with
    | .ipAddr _ => true
    | _ => false

end Verdict.Policy

-- !benchmark @start global_aux
namespace Verdict.Policy.Reference

-- Keep Rust's non-ASCII case folding behind the existing opaque primitive.
def lowerChar (c : Char) : List Char :=
  if c.toNat < 128 then [c.toLower] else Verdict.charLower c

-- Rust 1.86.0 (the fixed upstream toolchain) uses Unicode 16.0.0.
-- These merged ranges come from the Cased / Case_Ignorable properties in
-- https://www.unicode.org/Public/16.0.0/ucd/DerivedCoreProperties.txt
/-
UNICODE LICENSE V3

COPYRIGHT AND PERMISSION NOTICE

Copyright © 1991-2026 Unicode, Inc.

NOTICE TO USER: Carefully read the following legal agreement. BY
DOWNLOADING, INSTALLING, COPYING OR OTHERWISE USING DATA FILES, AND/OR
SOFTWARE, YOU UNEQUIVOCALLY ACCEPT, AND AGREE TO BE BOUND BY, ALL OF THE
TERMS AND CONDITIONS OF THIS AGREEMENT. IF YOU DO NOT AGREE, DO NOT
DOWNLOAD, INSTALL, COPY, DISTRIBUTE OR USE THE DATA FILES OR SOFTWARE.

Permission is hereby granted, free of charge, to any person obtaining a
copy of data files and any associated documentation (the "Data Files") or
software and any associated documentation (the "Software") to deal in the
Data Files or Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, and/or sell
copies of the Data Files or Software, and to permit persons to whom the
Data Files or Software are furnished to do so, provided that either (a)
this copyright and permission notice appear with all copies of the Data
Files or Software, or (b) this copyright and permission notice appear in
associated Documentation.

THE DATA FILES AND SOFTWARE ARE PROVIDED "AS IS", WITHOUT WARRANTY OF ANY
KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT OF
THIRD PARTY RIGHTS.

IN NO EVENT SHALL THE COPYRIGHT HOLDER OR HOLDERS INCLUDED IN THIS NOTICE
BE LIABLE FOR ANY CLAIM, OR ANY SPECIAL INDIRECT OR CONSEQUENTIAL DAMAGES,
OR ANY DAMAGES WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS,
WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION,
ARISING OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THE DATA
FILES OR SOFTWARE.

Except as contained in this notice, the name of a copyright holder shall
not be used in advertising or otherwise to promote the sale, use or other
dealings in these Data Files or Software without prior written
authorization of the copyright holder.
-/
def unicodeCasedRanges : List (Nat × Nat) :=
  [(0x41, 0x5A), (0x61, 0x7A), (0xAA, 0xAA), (0xB5, 0xB5),
   (0xBA, 0xBA), (0xC0, 0xD6), (0xD8, 0xF6), (0xF8, 0x1BA),
   (0x1BC, 0x1BF), (0x1C4, 0x293), (0x295, 0x2B8), (0x2C0, 0x2C1),
   (0x2E0, 0x2E4), (0x345, 0x345), (0x370, 0x373), (0x376, 0x377),
   (0x37A, 0x37D), (0x37F, 0x37F), (0x386, 0x386), (0x388, 0x38A),
   (0x38C, 0x38C), (0x38E, 0x3A1), (0x3A3, 0x3F5), (0x3F7, 0x481),
   (0x48A, 0x52F), (0x531, 0x556), (0x560, 0x588), (0x10A0, 0x10C5),
   (0x10C7, 0x10C7), (0x10CD, 0x10CD), (0x10D0, 0x10FA), (0x10FC, 0x10FF),
   (0x13A0, 0x13F5), (0x13F8, 0x13FD), (0x1C80, 0x1C8A), (0x1C90, 0x1CBA),
   (0x1CBD, 0x1CBF), (0x1D00, 0x1DBF), (0x1E00, 0x1F15), (0x1F18, 0x1F1D),
   (0x1F20, 0x1F45), (0x1F48, 0x1F4D), (0x1F50, 0x1F57), (0x1F59, 0x1F59),
   (0x1F5B, 0x1F5B), (0x1F5D, 0x1F5D), (0x1F5F, 0x1F7D), (0x1F80, 0x1FB4),
   (0x1FB6, 0x1FBC), (0x1FBE, 0x1FBE), (0x1FC2, 0x1FC4), (0x1FC6, 0x1FCC),
   (0x1FD0, 0x1FD3), (0x1FD6, 0x1FDB), (0x1FE0, 0x1FEC), (0x1FF2, 0x1FF4),
   (0x1FF6, 0x1FFC), (0x2071, 0x2071), (0x207F, 0x207F), (0x2090, 0x209C),
   (0x2102, 0x2102), (0x2107, 0x2107), (0x210A, 0x2113), (0x2115, 0x2115),
   (0x2119, 0x211D), (0x2124, 0x2124), (0x2126, 0x2126), (0x2128, 0x2128),
   (0x212A, 0x212D), (0x212F, 0x2134), (0x2139, 0x2139), (0x213C, 0x213F),
   (0x2145, 0x2149), (0x214E, 0x214E), (0x2160, 0x217F), (0x2183, 0x2184),
   (0x24B6, 0x24E9), (0x2C00, 0x2CE4), (0x2CEB, 0x2CEE), (0x2CF2, 0x2CF3),
   (0x2D00, 0x2D25), (0x2D27, 0x2D27), (0x2D2D, 0x2D2D), (0xA640, 0xA66D),
   (0xA680, 0xA69D), (0xA722, 0xA787), (0xA78B, 0xA78E), (0xA790, 0xA7CD),
   (0xA7D0, 0xA7D1), (0xA7D3, 0xA7D3), (0xA7D5, 0xA7DC), (0xA7F2, 0xA7F6),
   (0xA7F8, 0xA7FA), (0xAB30, 0xAB5A), (0xAB5C, 0xAB69), (0xAB70, 0xABBF),
   (0xFB00, 0xFB06), (0xFB13, 0xFB17), (0xFF21, 0xFF3A), (0xFF41, 0xFF5A),
   (0x10400, 0x1044F), (0x104B0, 0x104D3), (0x104D8, 0x104FB), (0x10570, 0x1057A),
   (0x1057C, 0x1058A), (0x1058C, 0x10592), (0x10594, 0x10595), (0x10597, 0x105A1),
   (0x105A3, 0x105B1), (0x105B3, 0x105B9), (0x105BB, 0x105BC), (0x10780, 0x10780),
   (0x10783, 0x10785), (0x10787, 0x107B0), (0x107B2, 0x107BA), (0x10C80, 0x10CB2),
   (0x10CC0, 0x10CF2), (0x10D50, 0x10D65), (0x10D70, 0x10D85), (0x118A0, 0x118DF),
   (0x16E40, 0x16E7F), (0x1D400, 0x1D454), (0x1D456, 0x1D49C), (0x1D49E, 0x1D49F),
   (0x1D4A2, 0x1D4A2), (0x1D4A5, 0x1D4A6), (0x1D4A9, 0x1D4AC), (0x1D4AE, 0x1D4B9),
   (0x1D4BB, 0x1D4BB), (0x1D4BD, 0x1D4C3), (0x1D4C5, 0x1D505), (0x1D507, 0x1D50A),
   (0x1D50D, 0x1D514), (0x1D516, 0x1D51C), (0x1D51E, 0x1D539), (0x1D53B, 0x1D53E),
   (0x1D540, 0x1D544), (0x1D546, 0x1D546), (0x1D54A, 0x1D550), (0x1D552, 0x1D6A5),
   (0x1D6A8, 0x1D6C0), (0x1D6C2, 0x1D6DA), (0x1D6DC, 0x1D6FA), (0x1D6FC, 0x1D714),
   (0x1D716, 0x1D734), (0x1D736, 0x1D74E), (0x1D750, 0x1D76E), (0x1D770, 0x1D788),
   (0x1D78A, 0x1D7A8), (0x1D7AA, 0x1D7C2), (0x1D7C4, 0x1D7CB), (0x1DF00, 0x1DF09),
   (0x1DF0B, 0x1DF1E), (0x1DF25, 0x1DF2A), (0x1E030, 0x1E06D), (0x1E900, 0x1E943),
   (0x1F130, 0x1F149), (0x1F150, 0x1F169), (0x1F170, 0x1F189)]

def unicodeCaseIgnorableRanges : List (Nat × Nat) :=
  [(0x27, 0x27), (0x2E, 0x2E), (0x3A, 0x3A), (0x5E, 0x5E),
   (0x60, 0x60), (0xA8, 0xA8), (0xAD, 0xAD), (0xAF, 0xAF),
   (0xB4, 0xB4), (0xB7, 0xB8), (0x2B0, 0x36F), (0x374, 0x375),
   (0x37A, 0x37A), (0x384, 0x385), (0x387, 0x387), (0x483, 0x489),
   (0x559, 0x559), (0x55F, 0x55F), (0x591, 0x5BD), (0x5BF, 0x5BF),
   (0x5C1, 0x5C2), (0x5C4, 0x5C5), (0x5C7, 0x5C7), (0x5F4, 0x5F4),
   (0x600, 0x605), (0x610, 0x61A), (0x61C, 0x61C), (0x640, 0x640),
   (0x64B, 0x65F), (0x670, 0x670), (0x6D6, 0x6DD), (0x6DF, 0x6E8),
   (0x6EA, 0x6ED), (0x70F, 0x70F), (0x711, 0x711), (0x730, 0x74A),
   (0x7A6, 0x7B0), (0x7EB, 0x7F5), (0x7FA, 0x7FA), (0x7FD, 0x7FD),
   (0x816, 0x82D), (0x859, 0x85B), (0x888, 0x888), (0x890, 0x891),
   (0x897, 0x89F), (0x8C9, 0x902), (0x93A, 0x93A), (0x93C, 0x93C),
   (0x941, 0x948), (0x94D, 0x94D), (0x951, 0x957), (0x962, 0x963),
   (0x971, 0x971), (0x981, 0x981), (0x9BC, 0x9BC), (0x9C1, 0x9C4),
   (0x9CD, 0x9CD), (0x9E2, 0x9E3), (0x9FE, 0x9FE), (0xA01, 0xA02),
   (0xA3C, 0xA3C), (0xA41, 0xA42), (0xA47, 0xA48), (0xA4B, 0xA4D),
   (0xA51, 0xA51), (0xA70, 0xA71), (0xA75, 0xA75), (0xA81, 0xA82),
   (0xABC, 0xABC), (0xAC1, 0xAC5), (0xAC7, 0xAC8), (0xACD, 0xACD),
   (0xAE2, 0xAE3), (0xAFA, 0xAFF), (0xB01, 0xB01), (0xB3C, 0xB3C),
   (0xB3F, 0xB3F), (0xB41, 0xB44), (0xB4D, 0xB4D), (0xB55, 0xB56),
   (0xB62, 0xB63), (0xB82, 0xB82), (0xBC0, 0xBC0), (0xBCD, 0xBCD),
   (0xC00, 0xC00), (0xC04, 0xC04), (0xC3C, 0xC3C), (0xC3E, 0xC40),
   (0xC46, 0xC48), (0xC4A, 0xC4D), (0xC55, 0xC56), (0xC62, 0xC63),
   (0xC81, 0xC81), (0xCBC, 0xCBC), (0xCBF, 0xCBF), (0xCC6, 0xCC6),
   (0xCCC, 0xCCD), (0xCE2, 0xCE3), (0xD00, 0xD01), (0xD3B, 0xD3C),
   (0xD41, 0xD44), (0xD4D, 0xD4D), (0xD62, 0xD63), (0xD81, 0xD81),
   (0xDCA, 0xDCA), (0xDD2, 0xDD4), (0xDD6, 0xDD6), (0xE31, 0xE31),
   (0xE34, 0xE3A), (0xE46, 0xE4E), (0xEB1, 0xEB1), (0xEB4, 0xEBC),
   (0xEC6, 0xEC6), (0xEC8, 0xECE), (0xF18, 0xF19), (0xF35, 0xF35),
   (0xF37, 0xF37), (0xF39, 0xF39), (0xF71, 0xF7E), (0xF80, 0xF84),
   (0xF86, 0xF87), (0xF8D, 0xF97), (0xF99, 0xFBC), (0xFC6, 0xFC6),
   (0x102D, 0x1030), (0x1032, 0x1037), (0x1039, 0x103A), (0x103D, 0x103E),
   (0x1058, 0x1059), (0x105E, 0x1060), (0x1071, 0x1074), (0x1082, 0x1082),
   (0x1085, 0x1086), (0x108D, 0x108D), (0x109D, 0x109D), (0x10FC, 0x10FC),
   (0x135D, 0x135F), (0x1712, 0x1714), (0x1732, 0x1733), (0x1752, 0x1753),
   (0x1772, 0x1773), (0x17B4, 0x17B5), (0x17B7, 0x17BD), (0x17C6, 0x17C6),
   (0x17C9, 0x17D3), (0x17D7, 0x17D7), (0x17DD, 0x17DD), (0x180B, 0x180F),
   (0x1843, 0x1843), (0x1885, 0x1886), (0x18A9, 0x18A9), (0x1920, 0x1922),
   (0x1927, 0x1928), (0x1932, 0x1932), (0x1939, 0x193B), (0x1A17, 0x1A18),
   (0x1A1B, 0x1A1B), (0x1A56, 0x1A56), (0x1A58, 0x1A5E), (0x1A60, 0x1A60),
   (0x1A62, 0x1A62), (0x1A65, 0x1A6C), (0x1A73, 0x1A7C), (0x1A7F, 0x1A7F),
   (0x1AA7, 0x1AA7), (0x1AB0, 0x1ACE), (0x1B00, 0x1B03), (0x1B34, 0x1B34),
   (0x1B36, 0x1B3A), (0x1B3C, 0x1B3C), (0x1B42, 0x1B42), (0x1B6B, 0x1B73),
   (0x1B80, 0x1B81), (0x1BA2, 0x1BA5), (0x1BA8, 0x1BA9), (0x1BAB, 0x1BAD),
   (0x1BE6, 0x1BE6), (0x1BE8, 0x1BE9), (0x1BED, 0x1BED), (0x1BEF, 0x1BF1),
   (0x1C2C, 0x1C33), (0x1C36, 0x1C37), (0x1C78, 0x1C7D), (0x1CD0, 0x1CD2),
   (0x1CD4, 0x1CE0), (0x1CE2, 0x1CE8), (0x1CED, 0x1CED), (0x1CF4, 0x1CF4),
   (0x1CF8, 0x1CF9), (0x1D2C, 0x1D6A), (0x1D78, 0x1D78), (0x1D9B, 0x1DFF),
   (0x1FBD, 0x1FBD), (0x1FBF, 0x1FC1), (0x1FCD, 0x1FCF), (0x1FDD, 0x1FDF),
   (0x1FED, 0x1FEF), (0x1FFD, 0x1FFE), (0x200B, 0x200F), (0x2018, 0x2019),
   (0x2024, 0x2024), (0x2027, 0x2027), (0x202A, 0x202E), (0x2060, 0x2064),
   (0x2066, 0x206F), (0x2071, 0x2071), (0x207F, 0x207F), (0x2090, 0x209C),
   (0x20D0, 0x20F0), (0x2C7C, 0x2C7D), (0x2CEF, 0x2CF1), (0x2D6F, 0x2D6F),
   (0x2D7F, 0x2D7F), (0x2DE0, 0x2DFF), (0x2E2F, 0x2E2F), (0x3005, 0x3005),
   (0x302A, 0x302D), (0x3031, 0x3035), (0x303B, 0x303B), (0x3099, 0x309E),
   (0x30FC, 0x30FE), (0xA015, 0xA015), (0xA4F8, 0xA4FD), (0xA60C, 0xA60C),
   (0xA66F, 0xA672), (0xA674, 0xA67D), (0xA67F, 0xA67F), (0xA69C, 0xA69F),
   (0xA6F0, 0xA6F1), (0xA700, 0xA721), (0xA770, 0xA770), (0xA788, 0xA78A),
   (0xA7F2, 0xA7F4), (0xA7F8, 0xA7F9), (0xA802, 0xA802), (0xA806, 0xA806),
   (0xA80B, 0xA80B), (0xA825, 0xA826), (0xA82C, 0xA82C), (0xA8C4, 0xA8C5),
   (0xA8E0, 0xA8F1), (0xA8FF, 0xA8FF), (0xA926, 0xA92D), (0xA947, 0xA951),
   (0xA980, 0xA982), (0xA9B3, 0xA9B3), (0xA9B6, 0xA9B9), (0xA9BC, 0xA9BD),
   (0xA9CF, 0xA9CF), (0xA9E5, 0xA9E6), (0xAA29, 0xAA2E), (0xAA31, 0xAA32),
   (0xAA35, 0xAA36), (0xAA43, 0xAA43), (0xAA4C, 0xAA4C), (0xAA70, 0xAA70),
   (0xAA7C, 0xAA7C), (0xAAB0, 0xAAB0), (0xAAB2, 0xAAB4), (0xAAB7, 0xAAB8),
   (0xAABE, 0xAABF), (0xAAC1, 0xAAC1), (0xAADD, 0xAADD), (0xAAEC, 0xAAED),
   (0xAAF3, 0xAAF4), (0xAAF6, 0xAAF6), (0xAB5B, 0xAB5F), (0xAB69, 0xAB6B),
   (0xABE5, 0xABE5), (0xABE8, 0xABE8), (0xABED, 0xABED), (0xFB1E, 0xFB1E),
   (0xFBB2, 0xFBC2), (0xFE00, 0xFE0F), (0xFE13, 0xFE13), (0xFE20, 0xFE2F),
   (0xFE52, 0xFE52), (0xFE55, 0xFE55), (0xFEFF, 0xFEFF), (0xFF07, 0xFF07),
   (0xFF0E, 0xFF0E), (0xFF1A, 0xFF1A), (0xFF3E, 0xFF3E), (0xFF40, 0xFF40),
   (0xFF70, 0xFF70), (0xFF9E, 0xFF9F), (0xFFE3, 0xFFE3), (0xFFF9, 0xFFFB),
   (0x101FD, 0x101FD), (0x102E0, 0x102E0), (0x10376, 0x1037A), (0x10780, 0x10785),
   (0x10787, 0x107B0), (0x107B2, 0x107BA), (0x10A01, 0x10A03), (0x10A05, 0x10A06),
   (0x10A0C, 0x10A0F), (0x10A38, 0x10A3A), (0x10A3F, 0x10A3F), (0x10AE5, 0x10AE6),
   (0x10D24, 0x10D27), (0x10D4E, 0x10D4E), (0x10D69, 0x10D6D), (0x10D6F, 0x10D6F),
   (0x10EAB, 0x10EAC), (0x10EFC, 0x10EFF), (0x10F46, 0x10F50), (0x10F82, 0x10F85),
   (0x11001, 0x11001), (0x11038, 0x11046), (0x11070, 0x11070), (0x11073, 0x11074),
   (0x1107F, 0x11081), (0x110B3, 0x110B6), (0x110B9, 0x110BA), (0x110BD, 0x110BD),
   (0x110C2, 0x110C2), (0x110CD, 0x110CD), (0x11100, 0x11102), (0x11127, 0x1112B),
   (0x1112D, 0x11134), (0x11173, 0x11173), (0x11180, 0x11181), (0x111B6, 0x111BE),
   (0x111C9, 0x111CC), (0x111CF, 0x111CF), (0x1122F, 0x11231), (0x11234, 0x11234),
   (0x11236, 0x11237), (0x1123E, 0x1123E), (0x11241, 0x11241), (0x112DF, 0x112DF),
   (0x112E3, 0x112EA), (0x11300, 0x11301), (0x1133B, 0x1133C), (0x11340, 0x11340),
   (0x11366, 0x1136C), (0x11370, 0x11374), (0x113BB, 0x113C0), (0x113CE, 0x113CE),
   (0x113D0, 0x113D0), (0x113D2, 0x113D2), (0x113E1, 0x113E2), (0x11438, 0x1143F),
   (0x11442, 0x11444), (0x11446, 0x11446), (0x1145E, 0x1145E), (0x114B3, 0x114B8),
   (0x114BA, 0x114BA), (0x114BF, 0x114C0), (0x114C2, 0x114C3), (0x115B2, 0x115B5),
   (0x115BC, 0x115BD), (0x115BF, 0x115C0), (0x115DC, 0x115DD), (0x11633, 0x1163A),
   (0x1163D, 0x1163D), (0x1163F, 0x11640), (0x116AB, 0x116AB), (0x116AD, 0x116AD),
   (0x116B0, 0x116B5), (0x116B7, 0x116B7), (0x1171D, 0x1171D), (0x1171F, 0x1171F),
   (0x11722, 0x11725), (0x11727, 0x1172B), (0x1182F, 0x11837), (0x11839, 0x1183A),
   (0x1193B, 0x1193C), (0x1193E, 0x1193E), (0x11943, 0x11943), (0x119D4, 0x119D7),
   (0x119DA, 0x119DB), (0x119E0, 0x119E0), (0x11A01, 0x11A0A), (0x11A33, 0x11A38),
   (0x11A3B, 0x11A3E), (0x11A47, 0x11A47), (0x11A51, 0x11A56), (0x11A59, 0x11A5B),
   (0x11A8A, 0x11A96), (0x11A98, 0x11A99), (0x11C30, 0x11C36), (0x11C38, 0x11C3D),
   (0x11C3F, 0x11C3F), (0x11C92, 0x11CA7), (0x11CAA, 0x11CB0), (0x11CB2, 0x11CB3),
   (0x11CB5, 0x11CB6), (0x11D31, 0x11D36), (0x11D3A, 0x11D3A), (0x11D3C, 0x11D3D),
   (0x11D3F, 0x11D45), (0x11D47, 0x11D47), (0x11D90, 0x11D91), (0x11D95, 0x11D95),
   (0x11D97, 0x11D97), (0x11EF3, 0x11EF4), (0x11F00, 0x11F01), (0x11F36, 0x11F3A),
   (0x11F40, 0x11F40), (0x11F42, 0x11F42), (0x11F5A, 0x11F5A), (0x13430, 0x13440),
   (0x13447, 0x13455), (0x1611E, 0x16129), (0x1612D, 0x1612F), (0x16AF0, 0x16AF4),
   (0x16B30, 0x16B36), (0x16B40, 0x16B43), (0x16D40, 0x16D42), (0x16D6B, 0x16D6C),
   (0x16F4F, 0x16F4F), (0x16F8F, 0x16F9F), (0x16FE0, 0x16FE1), (0x16FE3, 0x16FE4),
   (0x1AFF0, 0x1AFF3), (0x1AFF5, 0x1AFFB), (0x1AFFD, 0x1AFFE), (0x1BC9D, 0x1BC9E),
   (0x1BCA0, 0x1BCA3), (0x1CF00, 0x1CF2D), (0x1CF30, 0x1CF46), (0x1D167, 0x1D169),
   (0x1D173, 0x1D182), (0x1D185, 0x1D18B), (0x1D1AA, 0x1D1AD), (0x1D242, 0x1D244),
   (0x1DA00, 0x1DA36), (0x1DA3B, 0x1DA6C), (0x1DA75, 0x1DA75), (0x1DA84, 0x1DA84),
   (0x1DA9B, 0x1DA9F), (0x1DAA1, 0x1DAAF), (0x1E000, 0x1E006), (0x1E008, 0x1E018),
   (0x1E01B, 0x1E021), (0x1E023, 0x1E024), (0x1E026, 0x1E02A), (0x1E030, 0x1E06D),
   (0x1E08F, 0x1E08F), (0x1E130, 0x1E13D), (0x1E2AE, 0x1E2AE), (0x1E2EC, 0x1E2EF),
   (0x1E4EB, 0x1E4EF), (0x1E5EE, 0x1E5EF), (0x1E8D0, 0x1E8D6), (0x1E944, 0x1E94B),
   (0x1F3FB, 0x1F3FF), (0xE0001, 0xE0001), (0xE0020, 0xE007F), (0xE0100, 0xE01EF)]

def inRanges (value : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | (lo, hi) :: rest =>
    if value < lo then false else value ≤ hi || inRanges value rest

def isCased (c : Char) : Bool := inRanges c.toNat unicodeCasedRanges

def isCaseIgnorable (c : Char) : Bool := inRanges c.toNat unicodeCaseIgnorableRanges

def casedAfter (chars : List Char) : Bool :=
  (chars.dropWhile isCaseIgnorable).head?.any isCased

-- Rust alloc/src/str.rs:384-430: only capital sigma needs string context.
-- The mapping parameter lets tests exercise that same traversal while the
-- production wrapper preserves the existing opaque non-ASCII char mapping.
def lowerStringWith (lower : Char → List Char) (name : String) : String :=
  let rec go (previousCased : Bool) : List Char → List Char
    | [] => []
    | c :: cs =>
      let mapped := if c == 'Σ' then
          [if previousCased && !casedAfter cs then 'ς' else 'σ']
        else lower c
      let previousCased := if isCaseIgnorable c then previousCased else isCased c
      mapped ++ go previousCased cs
  String.ofList (go false name.toList)

def lowerString (name : String) : String := lowerStringWith lowerChar name

def normalizeName (name : String) : String :=
  let rec go : List Char -> Bool -> Bool -> List Char
    | [], _, _ => []
    | c :: cs, seenNonspace, seenSpace =>
      if c == ' ' then go cs seenNonspace true
      else
        let rest := lowerChar c ++ go cs true false
        if seenNonspace && seenSpace then ' ' :: rest else rest
  String.ofList (go name.toList false false)

-- Original common.rs:273-299 compares attributes and RDNs in order.
def sameAttr (a1 a2 : Attribute) (normalize : Bool) : Bool :=
  a1.oid == a2.oid &&
  if normalize then
    a1.value == a2.value || normalizeName a1.value == normalizeName a2.value
  else
    a1.value == a2.value

def sameRDN (rdn1 rdn2 : List Attribute) (normalize : Bool) : Bool :=
  rdn1.length == rdn2.length &&
  (rdn1.zip rdn2).all fun (a1, a2) => sameAttr a1 a2 normalize

def sameDN (dn1 dn2 : DistinguishedName) (normalize : Bool) : Bool :=
  dn1.rdns.length == dn2.rdns.length &&
  (dn1.rdns.zip dn2.rdns).all fun (r1, r2) => sameRDN r1 r2 normalize

-- Original common.rs:261-270 uses prefix RDNs and attribute containment.
def isSubtreeRDN (constraint target : List Attribute) (normalize : Bool) : Bool :=
  constraint.length <= target.length &&
  constraint.all (fun attr => target.any (fun candidate =>
    candidate.oid == attr.oid &&
    if normalize then normalizeName candidate.value == normalizeName attr.value
    else candidate.value == attr.value))

def isSubtreeOf (constraint target : DistinguishedName) (normalize : Bool) : Bool :=
  constraint.rdns.length <= target.rdns.length &&
  (constraint.rdns.zip target.rdns).all (fun (c, t) => isSubtreeRDN c t normalize)

-- Original common.rs:322-337 admits only IPv4 and IPv6 address/range pairs.
def ipAddrInRange (range addr : ByteArray) : Bool :=
  ((range.size == 8 && addr.size == 4) || (range.size == 32 && addr.size == 16)) &&
  Verdict.Policy.ipAddrInRange range addr

end Verdict.Policy.Reference
-- !benchmark @end global_aux

-- No benchmark APIs in this module — all content is curator-given
-- vocabulary consumed by the policy modules (Chrome / Firefox /
-- OpenSSL) and `Spec/Policy/Common.lean`.
