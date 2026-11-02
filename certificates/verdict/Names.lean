import Init.Data.String.Lemmas.Pattern.Memcmp
import Init.Data.String.Lemmas.IsEmpty
import Init.Data.String.Lemmas.Splits
import Init.Data.String.Lemmas.Pattern.Pred
import Init.Data.Iterators.Lemmas.Consumers.Loop
import Verdict.Spec.PolicyCommon

namespace VerdictCertificates.Names
open Verdict.Policy
open String.Slice.Pattern String.Slice.Pattern.Model

private theorem startsWith_append (p t : String) : (p ++ t).startsWith p = true := by
  change String.Slice.Pattern.ForwardSliceSearcher.startsWith p.toSlice (p ++ t).toSlice = true
  simp [String.Slice.Pattern.ForwardSliceSearcher.startsWith,
    String.Slice.Pattern.Internal.memcmpSlice_eq_true_iff, ByteArray.extract_append,
    -String.size_toByteArray]
  simp

theorem matchName_wildcard_base :
  ∀ (d : String), d ≠ "" → Verdict.Policy.matchName ("*." ++ d) d = true := by
  intro d hd
  have hp := startsWith_append "*." d
  have hlen : 0 < d.length := by
    have hn : d.length ≠ 0 := fun hz => hd (String.length_eq_zero_iff.mp hz)
    omega
  simp [matchName, hp, String.toList_append, String.length_append]
  change 2 < 2 + d.length
  omega

private theorem endsWith_append (p t : String) : (p ++ t).endsWith t = true := by
  change String.Slice.Pattern.BackwardSliceSearcher.endsWith t.toSlice (p ++ t).toSlice = true
  simp [String.Slice.Pattern.BackwardSliceSearcher.endsWith,
    String.Slice.Pattern.Internal.memcmpSlice_eq_true_iff, ByteArray.extract_append,
    -String.size_toByteArray]
  rw [show p.toByteArray.extract p.utf8ByteSize (p.utf8ByteSize + t.utf8ByteSize) = ByteArray.empty from
    ByteArray.extract_eq_empty_iff.mpr (by simp)]
  simp

theorem matchName_wildcard_single :
  ∀ (d x : String),
      d ≠ "" →
      x ≠ "" →
      ¬ x.any (· == '.') →
      Verdict.Policy.matchName ("*." ++ d) (x ++ "." ++ d) = true := by
  intro d x hd hx hdot
  have hp := startsWith_append "*." d
  have he : (x ++ "." ++ d).endsWith ("." ++ d) = true := by
    simpa [String.append_assoc] using endsWith_append x ("." ++ d)
  have hdx : 0 < d.length ∧ 0 < x.length := by
    constructor
    · have : d.length ≠ 0 := fun hz => hd (String.length_eq_zero_iff.mp hz)
      omega
    · have : x.length ≠ 0 := fun hz => hx (String.length_eq_zero_iff.mp hz)
      omega
  have hidx : (x ++ "." ++ d).length - (("*." ++ d).length - 1) = x.length := by
    simp only [String.length_append]
    change x.length + 1 + d.length - (2 + d.length - 1) = x.length
    omega
  have ht : String.ofList ((x ++ "." ++ d).toList.take x.length) = x := by
    simp [String.toList_append, List.take_append, ← String.length_toList]
  have hd1 : String.ofList (("*." ++ d).toList.drop 1) = "." ++ d := by
    apply String.toList_injective
    simp [String.toList_append]
  have hd2 : String.ofList (("*." ++ d).toList.drop 2) = d := by simp [String.toList_append]
  have hpl : 2 < ("*." ++ d).length := by
    simp only [String.length_append]
    change 2 < 2 + d.length
    omega
  have hnl : ("*." ++ d).length - 1 < (x ++ "." ++ d).length := by
    simp only [String.length_append]
    change 2 + d.length - 1 < x.length + 1 + d.length
    omega
  simp only [matchName, hp, ↓reduceIte]
  rw [hd1, hd2, hidx, ht]
  simp [hpl, hnl, he, hdot]
  constructor
  · change 2 < 2 + d.length
    omega
  · right
    change 2 + d.length - 1 < x.length + 1 + d.length
    omega

private theorem endsWith_split (s p : String) (h : s.endsWith p = true) : ∃ t, s = t ++ p := by
  change String.Slice.Pattern.BackwardSliceSearcher.endsWith p.toSlice s.toSlice = true at h
  simp [String.Slice.Pattern.BackwardSliceSearcher.endsWith,
    String.Slice.Pattern.Internal.memcmpSlice_eq_true_iff, -String.size_toByteArray] at h
  obtain ⟨hlen, hbytes⟩ := h
  have hbyte : s.toByteArray.extract (s.utf8ByteSize - p.utf8ByteSize) s.utf8ByteSize = p.toByteArray := by
    rw [Nat.sub_add_cancel hlen] at hbytes
    simpa [← String.size_toByteArray] using hbytes
  let pos : String.Pos.Raw := ⟨s.utf8ByteSize - p.utf8ByteSize⟩
  have hv : pos.IsValid s := by
    apply String.Pos.Raw.isValid_iff_isValidUTF8_extract_utf8ByteSize.mpr
    refine ⟨?_, ?_⟩
    · simp [pos, String.Pos.Raw.le_iff]
    · simpa [pos, hbyte] using p.isValidUTF8
  have hs : (s.sliceFrom (s.pos pos hv)).copy = p := by
    apply String.toByteArray_inj.mp
    simpa [String.Slice.toByteArray_copy, pos] using hbyte
  have ht := (s.pos pos hv).splits
  rw [hs] at ht
  exact ⟨_, ht.eq_append⟩

theorem permitName_dot_prefix :
    ∀ (suffix name : String),
      name.endsWith ("." ++ suffix) →
      Verdict.Policy.permitName ("." ++ suffix) name = true := by
  intro suffix name h
  obtain ⟨pre, rfl⟩ := endsWith_split name ("." ++ suffix) h
  have hp := startsWith_append "." suffix
  have hlen : ("." ++ suffix).length ≤ (pre ++ ("." ++ suffix)).length := by
    simp only [String.length_append]
    omega
  have hd : String.ofList ((pre ++ ("." ++ suffix)).toList.drop
      ((pre ++ ("." ++ suffix)).length - ("." ++ suffix).length)) = "." ++ suffix := by
    apply String.toList_injective
    simp [String.toList_append, String.length_append, ← String.length_toList]
  simp only [permitName, hp, ↓reduceIte]
  rw [hd]
  simp [hlen]

private theorem search_any_of_matches {ρ : Type} {pat : ρ} [ForwardPatternModel pat]
    {s : String.Slice} {start pos : s.Pos} {steps : List (SearchStep s)}
    (h : IsValidSearchFrom pat start steps) (hle : start ≤ pos) (hm : MatchesAt pat pos) :
    steps.any (fun step => match step with | .matched _ _ => true | .rejected _ _ => false) = true := by
  induction h with
  | endPos =>
    have hp : pos = s.endPos := Std.le_antisymm (by simp) hle
    subst pos
    obtain ⟨last, hl⟩ := hm.exists_isLongestMatchAt
    have := hl.lt
    have : last ≤ s.endPos := by simp
    exact False.elim ((Std.not_lt_of_ge this) hl.lt)
  | matched he ht ih => simp
  | mismatched he hno ht ih =>
    rename_i l startPos endPos
    by_cases hp : pos < endPos
    · exact False.elim (hno pos hle hp hm)
    · simpa using ih (Std.not_lt.mp hp)

private theorem any_of_matches (s : String) (p : Char → Bool) (pos : s.toSlice.Pos)
    (hm : MatchesAt p pos) : s.any p = true := by
  simp only [String.any, String.contains, String.Slice.contains]
  rw [← Std.Iter.any_toList]
  apply List.any_eq_true.mpr
  have hv : IsValidSearchFrom p s.toSlice.startPos (ToForwardSearcher.toSearcher p s.toSlice).toList :=
    LawfulToForwardSearcherModel.isValidSearchFrom_toList s.toSlice
  have hh := search_any_of_matches hv (String.Slice.Pos.startPos_le pos) hm
  obtain ⟨step, hs, hh⟩ := List.any_eq_true.mp hh
  refine ⟨step, hs, ?_⟩
  cases step <;> simp_all





private theorem any_middle (a b : String) (c : Char) (p : Char → Bool) (hp : p c = true) :
    (a ++ (String.singleton c ++ b)).any p = true := by
  let s := a ++ (String.singleton c ++ b)
  let pos : s.Pos := s.pos a.rawEndPos (String.Pos.Raw.isValid_rawEndPos.append_right _)
  have hsplit : pos.Splits a (String.singleton c ++ b) := String.Pos.splits_append_rawEndPos
  have hsplit' := hsplit.toSlice
  have hne : pos.toSlice ≠ s.toSlice.endPos := hsplit'.ne_endPos_of_singleton
  have hget : pos.toSlice.get hne = c := hsplit'.next.get_eq_of_singleton
  let rem := s.toSlice.sliceFrom pos.toSlice
  have hr : rem.startPos ≠ rem.endPos := by
    intro he
    have hh := congrArg String.Slice.Pos.ofSliceFrom he
    simp only [rem, String.Slice.Pos.ofSliceFrom_startPos, String.Slice.Pos.ofSliceFrom_endPos] at hh
    exact hne hh
  have hp' : p (rem.startPos.get hr) = true := by
    rw [String.Slice.Pos.get_eq_get_ofSliceFrom]
    simpa only [rem, String.Slice.Pos.ofSliceFrom_startPos, hget] using hp
  have hm : IsLongestMatch p (rem.startPos.next hr) :=
    String.Slice.Pattern.Model.CharPred.isLongestMatch_iff.mpr ⟨hr, rfl, hp'⟩
  apply any_of_matches s p pos.toSlice
  exact ⟨_, hm.isLongestMatchAt_ofSliceFrom⟩


theorem matchName_wildcard_multi :
    ∀ (d x y : String),
      x ≠ "" → y ≠ "" →
      ¬ x.any (· == '.') → ¬ y.any (· == '.') →
      Verdict.Policy.matchName ("*." ++ d) (x ++ "." ++ y ++ "." ++ d) = false := by
  intro d x y _ _ _ _
  have hp := startsWith_append "*." d
  have hd2 : String.ofList (("*." ++ d).toList.drop 2) = d := by simp [String.toList_append]
  have hidx : (x ++ "." ++ y ++ "." ++ d).length - (("*." ++ d).length - 1) =
      (x ++ "." ++ y).length := by
    simp only [String.length_append]
    change x.length + 1 + y.length + 1 + d.length - (2 + d.length - 1) = x.length + 1 + y.length
    omega
  have ht : String.ofList ((x ++ "." ++ y ++ "." ++ d).toList.take (x ++ "." ++ y).length) =
      x ++ "." ++ y := by
    rw [@String.append_assoc (x ++ "." ++ y) "." d, String.toList_append]
    simp only [← String.length_toList, List.take_left, String.ofList_toList]
  have ha : (x ++ "." ++ y).any (· == '.') = true := by
    simpa [String.append_assoc] using any_middle x y '.' (· == '.') (by decide)
  have hneq : d ≠ x ++ "." ++ y ++ "." ++ d := by
    intro he
    have hl := congrArg String.length he
    simp only [String.length_append] at hl
    change d.length = x.length + 1 + y.length + 1 + d.length at hl
    omega
  simp only [matchName, hp, ↓reduceIte]
  rw [hd2, hidx, ht, ha]
  simp [hneq]

end VerdictCertificates.Names
