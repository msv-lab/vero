import UnicodeV2.Spec.AbstractUnicodeStrings
import UnicodeV2.Spec.Unicode
import UnicodeV2.Spec.UnicodeEncodingForm
import UnicodeV2.Spec.UnicodeStringsWithoutUnicodeChar
import UnicodeV2.Spec.UnicodeStringsWithUnicodeChar
import UnicodeV2.Spec.Utf16EncodingForm
import UnicodeV2.Spec.Utf8EncodingForm
import UnicodeV2.Spec.Utf8EncodingScheme
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Dedup
import Aesop
set_option maxErrors 1000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000
set_option maxHeartbeats 30000
open Unicode
namespace UnicodeCertificates

macro "unfoldNoChar" n:ident : tactic => do
  let c := Lean.mkIdent (Lean.Name.str
    (Lean.Name.num `_private.UnicodeV2.Impl.UnicodeStringsWithoutUnicodeChar 0) n.getId.toString)
  `(tactic| unfold $c:ident)

macro "unfoldUEF" n:ident : tactic => do
  let c := Lean.mkIdent (Lean.Name.str
    (Lean.Name.num `_private.UnicodeV2.Impl.UnicodeEncodingForm 0) n.getId.toString)
  `(tactic| unfold $c:ident)


macro "uefPrivate" n:ident : term =>
  pure (Lean.mkIdent (Lean.Name.str
    (Lean.Name.num `_private.UnicodeV2.Impl.UnicodeEncodingForm 0) n.getId.toString))


theorem spec_utf8_encode_empty : _root_.spec_utf8_encode_empty canonical := by
  unfold _root_.spec_utf8_encode_empty
  intros
  rfl

theorem spec_utf8_decode_empty : _root_.spec_utf8_decode_empty canonical := by
  unfold _root_.spec_utf8_decode_empty
  intros
  rfl

theorem spec_utf16_encode_empty : _root_.spec_utf16_encode_empty canonical := by
  unfold _root_.spec_utf16_encode_empty
  intros
  rfl

theorem spec_utf16_decode_empty : _root_.spec_utf16_decode_empty canonical := by
  unfold _root_.spec_utf16_decode_empty
  intros
  rfl

theorem spec_noCharToUTF16_iff_noCharFromUTF16 : _root_.spec_noCharToUTF16_iff_noCharFromUTF16 canonical := by
  unfold _root_.spec_noCharToUTF16_iff_noCharFromUTF16
  intros
  rfl

theorem spec_noCharFromUTF16_iff_toUTF16 : _root_.spec_noCharFromUTF16_iff_toUTF16 canonical := by
  unfold _root_.spec_noCharFromUTF16_iff_toUTF16
  intros
  rfl

theorem Utf16__spec_split_prefix_empty_is_none : _root_.Utf16.spec_split_prefix_empty_is_none canonical := by
  unfold _root_.Utf16.spec_split_prefix_empty_is_none
  intros
  rfl

theorem spec_utf16_split_prefix_empty_is_none : _root_.spec_utf16_split_prefix_empty_is_none canonical := by
  unfold _root_.spec_utf16_split_prefix_empty_is_none
  intros
  rfl

theorem spec_serialize_deserialize : _root_.spec_serialize_deserialize canonical := by
  unfold _root_.spec_serialize_deserialize
  intros
  rfl

theorem spec_deserialize_serialize : _root_.spec_deserialize_serialize canonical := by
  unfold _root_.spec_deserialize_serialize
  intros
  rfl


theorem splitPrefix_inverts_prepend : _root_.spec_splitPrefix_inverts_prepend canonical := by
  intro m s h
  cases m with
  | nil => simp [canonical, Unicode.uefIsMinimalWellFormedCodeUnitSubsequence] at h
  | cons n ns =>
    cases ns with
    | nil => simpa [canonical, Unicode.uefIsMinimalWellFormedCodeUnitSubsequence,
        Unicode.uefSplitPrefixMinimalWellFormedCodeUnitSubsequence] using h
    | cons n' ns => simp [canonical, Unicode.uefIsMinimalWellFormedCodeUnitSubsequence] at h

theorem partition_minimal_is_singleton : _root_.spec_partition_minimal_is_singleton canonical := by
  intro m h
  cases m with
  | nil => simp [canonical, Unicode.uefIsMinimalWellFormedCodeUnitSubsequence] at h
  | cons n ns =>
    cases ns with
    | nil =>
      simp only [canonical, Unicode.uefIsMinimalWellFormedCodeUnitSubsequence] at h
      simp [canonical, Unicode.uefPartitionCodeUnitSequenceChecked, h]
    | cons n' ns => simp [canonical, Unicode.uefIsMinimalWellFormedCodeUnitSubsequence] at h

theorem minimal_implies_wellformed : _root_.spec_minimal_implies_wellformed canonical := by
  intro m hm
  unfold isWellFormedCodeUnitSequence
  rw [partition_minimal_is_singleton m hm]
  rfl

theorem partition_checked_agrees_with_partition : _root_.spec_partition_checked_agrees_with_partition canonical := by
  intro s parts h
  change Unicode.uefPartitionCodeUnitSequence s = parts
  simp [Unicode.uefPartitionCodeUnitSequence,
    show Unicode.uefPartitionCodeUnitSequenceChecked s = some parts from h]

theorem partition_append (s t : CodeUnitSeq) :
    Unicode.uefPartitionCodeUnitSequenceChecked (s ++ t) =
      (do
        let a ← Unicode.uefPartitionCodeUnitSequenceChecked s
        let b ← Unicode.uefPartitionCodeUnitSequenceChecked t
        pure (a ++ b)) := by
  simp [Unicode.uefPartitionCodeUnitSequenceChecked, List.mapM_append]

theorem concat_wellformed_is_wellformed : _root_.spec_concat_wellformed_is_wellformed canonical := by
  intro s t hs ht
  change (Unicode.uefPartitionCodeUnitSequenceChecked s).isSome = true at hs
  change (Unicode.uefPartitionCodeUnitSequenceChecked t).isSome = true at ht
  change (Unicode.uefPartitionCodeUnitSequenceChecked (s ++ t)).isSome = true
  rw [partition_append]
  cases hsp : Unicode.uefPartitionCodeUnitSequenceChecked s <;>
    cases htp : Unicode.uefPartitionCodeUnitSequenceChecked t <;> simp_all

theorem prepend_minimal_preserves_wellformed : _root_.spec_prepend_minimal_preserves_wellformed canonical := by
  intro m s hm hs
  exact concat_wellformed_is_wellformed m s (minimal_implies_wellformed m hm) hs

theorem flatten_minimal_is_wellformed : _root_.spec_flatten_minimal_is_wellformed canonical := by
  intro ms hm
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    exact prepend_minimal_preserves_wellformed m ms.flatten
      (hm m (by simp)) (ih (by intros; apply hm; simp_all))


theorem noCharToUTF8_empty : _root_.spec_noCharToUTF8_empty canonical := by
  change Unicode.noCharToUTF8Checked [] = some []
  unfold Unicode.noCharToUTF8Checked
  unfoldNoChar noChar_decodeUtf16
  rfl

theorem noCharFromUTF8_empty : _root_.spec_noCharFromUTF8_empty canonical := by
  change Unicode.noCharFromUTF8Checked [] = some []
  unfold Unicode.noCharFromUTF8Checked
  unfoldNoChar noChar_decodeUtf8
  rfl

theorem noCharToUTF16_empty : _root_.spec_noCharToUTF16_empty canonical := by
  change Unicode.noCharToUTF16Checked [] = some []
  unfold Unicode.noCharToUTF16Checked
  unfoldNoChar noChar_isWellFormedUtf16
  rfl

theorem noCharFromUTF16_empty : _root_.spec_noCharFromUTF16_empty canonical := by
  change Unicode.noCharFromUTF16Checked [] = some []
  unfold Unicode.noCharFromUTF16Checked
  unfoldNoChar noChar_isWellFormedUtf16
  rfl

theorem noCharToUTF16_returns_input : _root_.spec_noCharToUTF16_returns_input canonical := by
  intro s t h
  change Unicode.noCharToUTF16Checked s = some t at h
  unfold Unicode.noCharToUTF16Checked at h
  split at h <;> simp_all

theorem noCharFromUTF16_returns_input : _root_.spec_noCharFromUTF16_returns_input canonical := by
  intro s t h
  change Unicode.noCharFromUTF16Checked s = some t at h
  unfold Unicode.noCharFromUTF16Checked at h
  split at h <;> simp_all

theorem scalar_value_is_char : _root_.spec_scalar_value_is_char canonical := by
  intro sv
  have hbound := sv.val.property
  have hsur := sv.property
  simp only [HIGH_SURROGATE_MIN, HIGH_SURROGATE_MAX, LOW_SURROGATE_MIN, LOW_SURROGATE_MAX] at hsur
  dsimp
  omega

theorem char_is_unicode_scalar_value : _root_.spec_char_is_unicode_scalar_value canonical := by
  intro c
  have hc := c.valid
  simp only [isValidChar] at hc
  simp only [HIGH_SURROGATE_MIN, LOW_SURROGATE_MAX]
  change c.val.toNat ≤ 1114111 ∧ (c.val.toNat < 55296 ∨ 57343 < c.val.toNat)
  omega


theorem mapM_guard_eq_map {A B : Type} (p : A → Bool) (f : A → B)
    (xs : List A) (ys : List B)
    (h : xs.mapM (fun x => if p x then some (f x) else none) = some ys) :
    xs.map f = ys := by
  induction xs generalizing ys with
  | nil => simpa using h
  | cons x xs ih =>
    cases hp : p x
    · simp [List.mapM_cons, hp] at h
    · cases hs : xs.mapM (fun x => if p x then some (f x) else none) with
      | none => simp [List.mapM_cons, hp, hs] at h
      | some zs =>
        have he : f x :: zs = ys := by simpa [List.mapM_cons, hp, hs] using h
        simpa [ih zs hs] using he

theorem decode_checked_agrees_with_decode : _root_.spec_decode_checked_agrees_with_decode canonical := by
  intro s vs h
  exact mapM_guard_eq_map (uefPrivate isValidScalarCodePoint) (uefPrivate natToScalarValue) s vs h

theorem encode_decode_scalar_roundtrip : _root_.spec_encode_decode_scalar_roundtrip canonical := by
  intro v
  rcases v with ⟨⟨n, hn⟩, hv⟩
  change Unicode.uefDecodeMinimalWellFormedCodeUnitSubsequence (Unicode.uefEncodeScalarValue _) = _
  unfold Unicode.uefEncodeScalarValue Unicode.uefDecodeMinimalWellFormedCodeUnitSubsequence
  unfoldUEF natToScalarValue
  simp [hn, hv]

theorem encode_sequence_is_wellformed : _root_.spec_encode_sequence_is_wellformed canonical := by
  intro vs
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change isWellFormedCodeUnitSequence canonical ([v.val.val] ++ Unicode.uefEncodeScalarSequence vs) = true
    apply prepend_minimal_preserves_wellformed
    · change Unicode.uefIsMinimalWellFormedCodeUnitSubsequence [v.val.val] = true
      unfold Unicode.uefIsMinimalWellFormedCodeUnitSubsequence
      unfoldUEF isValidScalarCodePoint
      have hv := v.property
      have hn := v.val.property
      simp only [HIGH_SURROGATE_MIN, HIGH_SURROGATE_MAX, LOW_SURROGATE_MIN, LOW_SURROGATE_MAX, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hv ⊢
      simp_all [HIGH_SURROGATE_MIN, HIGH_SURROGATE_MAX, LOW_SURROGATE_MIN, LOW_SURROGATE_MAX] <;> omega
    · exact ih

end UnicodeCertificates
