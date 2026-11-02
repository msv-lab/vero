import Verdict.Spec.Issue

namespace VerdictCertificates.Normalization

private theorem go_leading (chars : List Char) (ws : Bool) :
    (Verdict.normalizeString.go false ws chars).head? ≠ some ' ' := by
  induction chars generalizing ws with
  | nil => simp [Verdict.normalizeString.go]
  | cons c cs ih =>
    by_cases hc : c = ' '
    · simpa [Verdict.normalizeString.go, hc] using ih true
    · simp [Verdict.normalizeString.go, hc]

private theorem cons_trailing (c : Char) (chars : List Char) (hc : c ≠ ' ')
    (ht : chars.getLast? ≠ some ' ') : (c :: chars).getLast? ≠ some ' ' := by
  cases chars with
  | nil => simpa using hc
  | cons d ds => simpa only [List.getLast?_cons_cons] using ht

private theorem go_trailing (chars : List Char) (nw ws : Bool) :
    (Verdict.normalizeString.go nw ws chars).getLast? ≠ some ' ' := by
  induction chars generalizing nw ws with
  | nil => simp [Verdict.normalizeString.go]
  | cons c cs ih =>
    by_cases hc : c = ' '
    · simpa [Verdict.normalizeString.go, hc] using ih nw true
    · simp only [Verdict.normalizeString.go, hc, ↓reduceIte]
      split
      · simpa only [List.getLast?_cons_cons] using cons_trailing c _ hc (ih true false)
      · exact cons_trailing c _ hc (ih true false)

theorem normalize_noLeading :
  ∀ (s : String),
      let ns := Verdict.normalizeString s
      (ns.toList).head? ≠ some ' ' := by
  intro s
  simpa [Verdict.normalizeString] using go_leading (s.toList.flatMap Verdict.charLower) false

theorem normalize_noTrailing :
  ∀ (s : String),
      (∀ c, c ∈ s.toList → c.val ≥ 0x20 ∧ c.val ≤ 0x7E) →
      let ns := Verdict.normalizeString s
      (ns.toList).getLast? ≠ some ' ' := by
  intro s _
  simpa [Verdict.normalizeString] using go_trailing (s.toList.flatMap Verdict.charLower) false false

theorem normalize_empty :
  Verdict.normalizeString "" = "" := by rfl

end VerdictCertificates.Normalization
