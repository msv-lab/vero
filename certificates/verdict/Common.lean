import Verdict.Spec.PolicyCommon

namespace VerdictCertificates.Common
open Verdict.Policy

theorem sameAttr_normalize :
  ∀ (a1 a2 : Verdict.Policy.Attribute),
      Verdict.Policy.sameAttr a1 a2 true = true →
      (a1.oid = a2.oid ∧
       (a1.value = a2.value ∨
        Verdict.Policy.normalizeString a1.value
          = Verdict.Policy.normalizeString a2.value)) := by
  intro a b h
  simpa [sameAttr] using h

theorem sameAttr_exact :
  ∀ (a1 a2 : Verdict.Policy.Attribute),
      Verdict.Policy.sameAttr a1 a2 false = true ↔
        a1.oid = a2.oid ∧ a1.value = a2.value := by
  intro a b
  simp [sameAttr]

private def zipRel {α : Type} (r : α → α → Bool) (xs ys : List α) : Bool :=
  xs.length == ys.length && (xs.zip ys).all (fun p => r p.1 p.2)

private theorem zipRel_cons {α : Type} (r : α → α → Bool) (x y : α) (xs ys : List α) :
    zipRel r (x :: xs) (y :: ys) = (r x y && zipRel r xs ys) := by
  simp [zipRel, Bool.and_assoc, Bool.and_left_comm]

private theorem zipRel_refl {α : Type} (r : α → α → Bool)
    (hr : ∀ x, r x x = true) (xs : List α) : zipRel r xs xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [zipRel_cons, hr, ih]

private theorem zipRel_symm {α : Type} (r : α → α → Bool)
    (hr : ∀ x y, r x y = r y x) (xs ys : List α) : zipRel r xs ys = zipRel r ys xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [zipRel]
  | cons x xs ih =>
    cases ys with
    | nil => simp [zipRel]
    | cons y ys => simp [zipRel_cons, hr x y, ih]

private theorem zipRel_trans {α : Type} (r : α → α → Bool)
    (hr : ∀ x y z, r x y = true → r y z = true → r x z = true)
    (xs ys zs : List α) :
    zipRel r xs ys = true → zipRel r ys zs = true → zipRel r xs zs = true := by
  induction xs generalizing ys zs with
  | nil => cases ys <;> cases zs <;> simp [zipRel]
  | cons x xs ih =>
    cases ys with
    | nil => simp [zipRel]
    | cons y ys =>
      cases zs with
      | nil => simp [zipRel]
      | cons z zs =>
        simp only [zipRel_cons, Bool.and_eq_true_iff]
        intro h₁ h₂
        exact ⟨hr x y z h₁.1 h₂.1, ih ys zs h₁.2 h₂.2⟩

private theorem attr_refl (a : Attribute) (norm : Bool) : sameAttr a a norm = true := by
  cases norm <;> simp [sameAttr]

private theorem attr_symm (a b : Attribute) (norm : Bool) : sameAttr a b norm = sameAttr b a norm := by
  cases norm <;> simp only [sameAttr] <;> grind

private theorem attr_trans (a b c : Attribute) (norm : Bool) :
    sameAttr a b norm = true → sameAttr b c norm = true → sameAttr a c norm = true := by
  cases norm <;> simp only [sameAttr, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true_iff,
    Bool.or_eq_true_iff, beq_iff_eq]
  all_goals grind

private theorem rdn_refl (rdn : List Attribute) (norm : Bool) : sameRDN rdn rdn norm = true :=
  zipRel_refl (fun a b => sameAttr a b norm) (fun a => attr_refl a norm) rdn

private theorem rdn_symm (a b : List Attribute) (norm : Bool) : sameRDN a b norm = sameRDN b a norm :=
  zipRel_symm (fun a b => sameAttr a b norm) (fun a b => attr_symm a b norm) a b

private theorem rdn_trans (a b c : List Attribute) (norm : Bool) :
    sameRDN a b norm = true → sameRDN b c norm = true → sameRDN a c norm = true :=
  zipRel_trans (fun a b => sameAttr a b norm) (fun a b c => attr_trans a b c norm) a b c

theorem sameDN_refl :
  ∀ (dn : Verdict.Policy.DistinguishedName) (norm : Bool),
      Verdict.Policy.sameDN dn dn norm = true := by
  intro dn norm
  exact zipRel_refl (fun a b => sameRDN a b norm) (fun a => rdn_refl a norm) dn.rdns

theorem sameDN_symm :
  ∀ (dn1 dn2 : Verdict.Policy.DistinguishedName) (norm : Bool),
      Verdict.Policy.sameDN dn1 dn2 norm = Verdict.Policy.sameDN dn2 dn1 norm := by
  intro a b norm
  exact zipRel_symm (fun a b => sameRDN a b norm) (fun a b => rdn_symm a b norm) a.rdns b.rdns

theorem sameDN_trans :
  ∀ (dn1 dn2 dn3 : Verdict.Policy.DistinguishedName) (norm : Bool),
      Verdict.Policy.sameDN dn1 dn2 norm = true →
      Verdict.Policy.sameDN dn2 dn3 norm = true →
      Verdict.Policy.sameDN dn1 dn3 norm = true := by
  intro a b c norm
  exact zipRel_trans (fun a b => sameRDN a b norm) (fun a b c => rdn_trans a b c norm) a.rdns b.rdns c.rdns

theorem sameDN_lengthMismatch :
  ∀ (dn1 dn2 : Verdict.Policy.DistinguishedName) (norm : Bool),
      dn1.rdns.length ≠ dn2.rdns.length →
      Verdict.Policy.sameDN dn1 dn2 norm = false := by
  intro a b norm h
  simp [sameDN, h]

theorem matchName_exact :
  ∀ (pattern name : String),
      pattern ≠ name →
      ¬ pattern.startsWith "*." →
      Verdict.Policy.matchName pattern name = false := by
  intro pattern name hn hw
  simp [matchName, hw, hn]

theorem permitName_empty :
  ∀ (name : String), Verdict.Policy.permitName "" name = true := by
  intro name
  rfl

theorem ipRange_ipv4 :
  ∀ (range addr : ByteArray),
      range.size = 8 → addr.size = 4 →
      (Verdict.Policy.ipAddrInRange range addr = true ↔
       ∀ i : Nat, i < 4 →
         (range[i]! &&& range[i + 4]!) = (addr[i]! &&& range[i + 4]!)) := by
  intro range addr hr ha
  simp [ipAddrInRange, hr, ha, List.all_eq_true, List.mem_range]

theorem authKeyId_noAki :
  ∀ (issuer subject : Verdict.Policy.AbstractCertificate),
      subject.extAuthorityKeyId = none →
      Verdict.Policy.checkAuthKeyId issuer subject = true := by
  intro issuer subject h
  simp [checkAuthKeyId, h]

theorem authKeyId_match :
  ∀ (issuer subject : Verdict.Policy.AbstractCertificate) (kid : String),
      issuer.extSubjectKeyId = some { critical := none, keyId := kid } →
      subject.extAuthorityKeyId =
        some { critical := none, keyId := some kid, issuer := none, serial := none } →
      Verdict.Policy.checkAuthKeyId issuer subject = true := by
  intro issuer subject kid h₁ h₂
  simp [checkAuthKeyId, h₁, h₂]

theorem authKeyId_mismatch :
  ∀ (issuer subject : Verdict.Policy.AbstractCertificate) (k1 k2 : String),
      k1 ≠ k2 →
      issuer.extSubjectKeyId = some { critical := none, keyId := k1 } →
      subject.extAuthorityKeyId =
        some { critical := none, keyId := some k2, issuer := none, serial := none } →
      Verdict.Policy.checkAuthKeyId issuer subject = false := by
  intro issuer subject k₁ k₂ hn h₁ h₂
  simp [checkAuthKeyId, h₁, h₂, hn]

theorem duplicateExtensions_none :
  ∀ (cert : Verdict.Policy.AbstractCertificate),
      cert.allExts = none →
      Verdict.Policy.checkDuplicateExtensions cert = true := by
  intro cert h
  simp [checkDuplicateExtensions, h]

private theorem zipRel_mono {α : Type} (r s : α → α → Bool)
    (hr : ∀ a b, r a b = true → s a b = true) (xs ys : List α)
    (h : zipRel r xs ys = true) : zipRel s xs ys = true := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [zipRel]
  | cons x xs ih =>
    cases ys with
    | nil => simp [zipRel] at h
    | cons y ys =>
      simp only [zipRel_cons, Bool.and_eq_true_iff] at h ⊢
      exact ⟨hr x y h.1, ih ys h.2⟩

theorem sameDN_strict_normalized :
  ∀ (dn1 dn2 : Verdict.Policy.DistinguishedName),
      Verdict.Policy.sameDN dn1 dn2 false = true →
      Verdict.Policy.sameDN dn1 dn2 true = true := by
  intro a b h
  apply zipRel_mono (fun a b => sameRDN a b false) (fun a b => sameRDN a b true) _ a.rdns b.rdns h
  intro a b h
  apply zipRel_mono (fun a b => sameAttr a b false) (fun a b => sameAttr a b true) _ a b h
  intro a b h
  simp_all [sameAttr]

private theorem zipRel_iff {α : Type} [Inhabited α] (r : α → α → Bool) (xs ys : List α) :
    zipRel r xs ys = true ↔ xs.length = ys.length ∧
      ∀ i, i < xs.length → r xs[i]! ys[i]! = true := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [zipRel]
  | cons x xs ih =>
    cases ys with
    | nil => simp [zipRel]
    | cons y ys =>
      simp only [zipRel_cons, Bool.and_eq_true_iff, ih, List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨hr, hlen, hall⟩
        refine ⟨hlen, ?_⟩
        intro i hi
        cases i with
        | zero => simpa using hr
        | succ i => simpa using hall i (by omega)
      · rintro ⟨hlen, hall⟩
        exact ⟨by simpa using hall 0 (by omega), hlen, fun i hi => by simpa using hall (i+1) (by omega)⟩

theorem sameDN_iff :
  ∀ (dn1 dn2 : Verdict.Policy.DistinguishedName) (norm : Bool),
      Verdict.Policy.sameDN dn1 dn2 norm = true ↔
        dn1.rdns.length = dn2.rdns.length ∧
        ∀ i, (hi : i < dn1.rdns.length) →
          Verdict.Policy.sameRDN dn1.rdns[i]! dn2.rdns[i]! norm = true := by
  intro a b norm
  exact zipRel_iff (fun a b => sameRDN a b norm) a.rdns b.rdns

end VerdictCertificates.Common
