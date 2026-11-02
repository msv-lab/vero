import Aesop
import JsonPatch.Spec.Pointer

set_option maxHeartbeats 2000
open JsonPatch

private theorem objGet_reference (kvs : List (String × Json)) (k : String) : objGet kvs k = refObjGet kvs k := by
  induction kvs with
  | nil => rfl
  | cons p rest ih => cases p; simp [objGet, refObjGet, ih]

private theorem walk_reference (d : Json) (p : String) : walk d p = refWalk d p := by
  cases d <;> simp [walk, refWalk, objGet_reference, arrIndex, refArrIndex, isDigits, refIsDigits] <;> rfl

private theorem resolve_reference (ps : List String) (d : Json) : resolveParts d ps = refResolveParts d ps := by
  induction ps generalizing d with
  | nil => rfl
  | cons p ps ih =>
    simp only [resolveParts, refResolveParts, walk_reference]
    cases refWalk d p <;> simp [ih]

private theorem escape_reference (cs : List Char) : escapeChars cs = refEscapeChars cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [escapeChars, refEscapeChars, ih]

private theorem unescape_escape_chars (cs : List Char) : unescapeChars (escapeChars cs) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    by_cases ht : c = '~'
    · simp [escapeChars, ht, unescapeChars, ih]
    · by_cases hs : c = '/'
      · simp [escapeChars, hs, unescapeChars, ih]
      · simp [escapeChars, ht, hs, unescapeChars, ih]

theorem manual_spec_unescape_escape_roundtrip : spec_unescape_escape_roundtrip canonical := by
  intro s
  change unescape (escape s) = s
  simp [unescape, escape, unescape_escape_chars]
#print axioms manual_spec_unescape_escape_roundtrip

theorem manual_spec_escape_chars : spec_escape_chars canonical := by
  intro s
  change String.ofList (escapeChars s.toList) = String.ofList (refEscapeChars s.toList)
  rw [escape_reference]
#print axioms manual_spec_escape_chars

theorem manual_spec_resolve_walk : spec_resolve_walk canonical := by
  intro d ps
  exact resolve_reference ps d
#print axioms manual_spec_resolve_walk

theorem manual_spec_resolve_nil : spec_resolve_nil canonical := by
  intro d
  rfl
#print axioms manual_spec_resolve_nil

theorem manual_spec_resolve_obj_step : spec_resolve_obj_step canonical := by
  intro kvs k rest
  change resolveParts (.obj kvs) (k :: rest) = _
  simp only [resolveParts, walk, objGet_reference]
  cases refObjGet kvs k <;> simp [resolve_reference]
#print axioms manual_spec_resolve_obj_step

theorem manual_spec_resolve_append_bind : spec_resolve_append_bind canonical := by
  intro d p1 p2
  change resolveParts d (p1 ++ p2) = (match resolveParts d p1 with | some d' => resolveParts d' p2 | none => none)
  induction p1 generalizing d with
  | nil => rfl
  | cons p ps ih =>
    change resolveParts d ((p :: ps) ++ p2) = (match resolveParts d (p :: ps) with | some d' => resolveParts d' p2 | none => none)
    simp only [List.cons_append, resolveParts]
    cases walk d p <;> simp [ih]
#print axioms manual_spec_resolve_append_bind

private theorem escapeChars_append (a b : List Char) : escapeChars (a ++ b) = escapeChars a ++ escapeChars b := by
  induction a with
  | nil => rfl
  | cons c a ih =>
    by_cases ht : c = '~'
    · simp [escapeChars, ht, ih]
    · by_cases hs : c = '/'
      · simp [escapeChars, ht, hs, ih, eq_comm]
      · simp [escapeChars, ht, hs, ih, eq_comm]

theorem manual_spec_escape_append_hom : spec_escape_append_hom canonical := by
  intro a b
  change escape (a ++ b) = escape a ++ escape b
  simp [escape, escapeChars_append, String.ofList_append]
#print axioms manual_spec_escape_append_hom

private theorem escapeChars_no_slash (cs : List Char) : '/' ∉ escapeChars cs := by
  induction cs with
  | nil => simp [escapeChars]
  | cons c cs ih =>
    by_cases ht : c = '~'
    · simp [escapeChars, ht, ih]
    · by_cases hs : c = '/'
      · simp [escapeChars, ht, hs, ih, eq_comm]
      · simp [escapeChars, ht, hs, ih, eq_comm]

theorem manual_spec_escape_no_raw_slash : spec_escape_no_raw_slash canonical := by
  intro s
  change ¬ (escape s).toList.contains '/'
  simpa [escape] using escapeChars_no_slash s.toList
#print axioms manual_spec_escape_no_raw_slash
