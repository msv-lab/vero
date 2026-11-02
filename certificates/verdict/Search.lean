import Verdict.Spec.Validator

namespace VerdictCertificates.Search
open Verdict

private def Witness
    (bundle : List Verdict.Certificate)
    (roots  : List Verdict.Certificate)
    (path   : Verdict.BundlePath)
    (rootIdx : Nat) : Prop :=
  path ≠ [] ∧
  path.head? = some 0 ∧
  Verdict.isSimplePath path = true ∧
  Verdict.pathInBounds path bundle.length = true ∧
  rootIdx < roots.length ∧
  (∀ i, i + 1 < path.length →
    Verdict.issuedByRaw
      bundle[path[i+1]!]! bundle[path[i]!]! = true) ∧
  (match path.getLast? with
   | some lastIdx =>
       Verdict.issuedByRaw roots[rootIdx]! bundle[lastIdx]! = true
   | none => False)


private def Walk (bundle roots : List Certificate) (current : Nat) : List Nat → Prop
  | [] => ∃ r, r < roots.length ∧ issuedByRaw roots[r]! bundle[current]! = true
  | next :: tail => issuedByRaw bundle[next]! bundle[current]! = true ∧ Walk bundle roots next tail

private theorem root_any (bundle roots : List Certificate) (current : Nat) :
    roots.any (fun root => issuedByRaw root bundle[current]!) = true ↔ Walk bundle roots current [] := by
  simp only [List.any_eq_true, Walk]
  constructor
  · rintro ⟨root, hm, h⟩
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    exact ⟨i, hi, by simpa [List.getElem?_eq_getElem hi, he] using h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨roots[i], List.getElem_mem hi, by simpa [List.getElem?_eq_getElem hi] using h⟩

private theorem search_sound (bundle roots : List Certificate) (fuel : Nat)
    (remaining : List Nat) (current : Nat) (hn : remaining.Nodup) (hc : current ∉ remaining)
    (h : searchChain bundle roots fuel remaining current = true) :
    ∃ tail, (current :: tail).Nodup ∧ (∀ i, i ∈ tail → i ∈ remaining) ∧ Walk bundle roots current tail := by
  induction fuel generalizing remaining current with
  | zero =>
    exact ⟨[], by simp, by simp, (root_any bundle roots current).mp h⟩
  | succ fuel ih =>
    simp only [searchChain, Bool.or_eq_true_iff] at h
    rcases h with h | h
    · exact ⟨[], by simp, by simp, (root_any bundle roots current).mp h⟩
    · obtain ⟨next, hm, he, hs⟩ := (by simpa only [List.any_eq_true, Bool.and_eq_true_iff] using h)
      obtain ⟨tail, hnd, hsub, hw⟩ := ih (remaining.erase next) next (List.Nodup.erase next hn)
        (hn.not_mem_erase) hs
      refine ⟨next :: tail, ?_, ?_, he, hw⟩
      · apply List.nodup_cons.mpr
        refine ⟨?_, hnd⟩
        intro hm'
        rcases List.mem_cons.mp hm' with heq | ht
        · subst next; exact hc hm
        · exact hc (List.mem_of_mem_erase (hsub current ht))
      · intro i hi
        rcases List.mem_cons.mp hi with heq | ht
        · simpa [heq] using hm
        · exact List.mem_of_mem_erase (hsub i ht)

private theorem search_complete (bundle roots : List Certificate) (fuel : Nat)
    (remaining : List Nat) (current : Nat) (tail : List Nat)
    (hn : tail.Nodup) (hsub : ∀ i, i ∈ tail → i ∈ remaining)
    (hlen : tail.length ≤ fuel) (hw : Walk bundle roots current tail) :
    searchChain bundle roots fuel remaining current = true := by
  induction fuel generalizing remaining current tail with
  | zero =>
    have ht : tail = [] := List.length_eq_zero_iff.mp (by omega)
    subst tail
    exact (root_any bundle roots current).mpr hw
  | succ fuel ih =>
    simp only [searchChain, Bool.or_eq_true_iff]
    cases tail with
    | nil => exact Or.inl ((root_any bundle roots current).mpr hw)
    | cons next tail =>
      right
      apply List.any_eq_true.mpr
      refine ⟨next, hsub next (by simp), Bool.and_eq_true_iff.mpr ⟨hw.1, ?_⟩⟩
      apply ih (remaining.erase next) next tail (List.nodup_cons.mp hn).2
      · intro i hi
        apply (List.mem_erase_of_ne (by
          intro he; subst i; exact (List.nodup_cons.mp hn).1 hi)).mpr
        exact hsub i (by simp [hi])
      · simp only [List.length_cons] at hlen
        omega
      · exact hw.2

private def Links (bundle roots : List Certificate) (path : List Nat) : Prop :=
  (∀ i, i + 1 < path.length → issuedByRaw bundle[path[i+1]!]! bundle[path[i]!]! = true) ∧
  ∃ r, r < roots.length ∧ (match path.getLast? with
    | some last => issuedByRaw roots[r]! bundle[last]! = true
    | none => False)

private theorem walk_links (bundle roots : List Certificate) (current : Nat) (tail : List Nat) :
    Walk bundle roots current tail ↔ Links bundle roots (current :: tail) := by
  induction tail generalizing current with
  | nil => simp [Walk, Links]
  | cons next tail ih =>
    rw [Walk, ih]
    unfold Links
    simp only [List.length_cons, List.getLast?_cons_cons]
    constructor
    · rintro ⟨he, hall, hr⟩
      refine ⟨?_, hr⟩
      intro i hi
      cases i with
      | zero => simpa using he
      | succ i => simpa using hall i (by omega)
    · rintro ⟨hall, hr⟩
      refine ⟨by simpa using hall 0 (by omega), ?_, hr⟩
      intro i hi
      simpa using hall (i+1) (by omega)

private theorem nodup_subset_length (xs ys : List Nat) (hn : xs.Nodup)
    (hs : ∀ i, i ∈ xs → i ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have hx : x ∈ ys := hs x (by simp)
    have ht := ih (ys.erase x) (List.nodup_cons.mp hn).2 (by
      intro i hi
      apply (List.mem_erase_of_ne (by intro he; subst i; exact (List.nodup_cons.mp hn).1 hi)).mpr
      exact hs i (by simp [hi]))
    have hl := List.length_erase_of_mem hx
    have hp := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

theorem validator_sound :
  ∀ (rootsB64 bundleB64 : List Verdict.Bytes) (task : Verdict.Task),
      Verdict.validateX509Base64 rootsB64 bundleB64 task = .ok true →
      let roots  := rootsB64.filterMap Verdict.parseX509Base64
      let bundle := bundleB64.filterMap Verdict.parseX509Base64
      bundle ≠ [] ∧
      ∃ (path : Verdict.BundlePath) (rootIdx : Nat),
        Witness bundle roots path rootIdx := by
  intro rootsB64 bundleB64 task h
  change Verdict.validateX509Base64 rootsB64 bundleB64 task = .ok true at h
  change (let roots := rootsB64.filterMap Verdict.parseX509Base64; let bundle := bundleB64.filterMap Verdict.parseX509Base64; bundle ≠ [] ∧ ∃ path r, Witness bundle roots path r)
  dsimp only
  simp only [Verdict.validateX509Base64] at h
  generalize hr : rootsB64.filterMap Verdict.parseX509Base64 = roots at h ⊢
  generalize hb : bundleB64.filterMap Verdict.parseX509Base64 = bundle at h ⊢
  change bundle ≠ [] ∧ ∃ path r, Witness bundle roots path r
  by_cases he : bundle = []
  · simp [he] at h
  have hp : 0 < bundle.length := List.length_pos_iff.mpr he
  have hs : searchChain bundle roots (bundle.length - 1) ((List.range bundle.length).erase 0) 0 = true := by
    simpa [List.isEmpty_eq_false_iff.mpr he] using h
  obtain ⟨tail, hn, hsub, hw⟩ := search_sound bundle roots (bundle.length - 1)
    ((List.range bundle.length).erase 0) 0 (List.Nodup.erase 0 (List.nodup_range))
    ((List.nodup_range).not_mem_erase) hs
  obtain ⟨hedges, r, hr', hroot⟩ := (walk_links bundle roots 0 tail).mp hw
  refine ⟨he, 0 :: tail, r, ?_⟩
  refine ⟨by simp, rfl, ?_, ?_, hr', hedges, hroot⟩
  · simpa [Verdict.isSimplePath] using hn
  · change (0 :: tail).all (fun i => decide (i < bundle.length)) = true
    apply List.all_eq_true.mpr
    intro i hi
    apply decide_eq_true
    rcases List.mem_cons.mp hi with hzero | ht
    · simpa [hzero] using hp
    · exact List.mem_range.mp (List.mem_of_mem_erase (hsub i ht))

theorem validator_complete :
  ∀ (rootsB64 bundleB64 : List Verdict.Bytes) (task : Verdict.Task),
      let roots  := rootsB64.filterMap Verdict.parseX509Base64
      let bundle := bundleB64.filterMap Verdict.parseX509Base64
      (∃ (path : Verdict.BundlePath) (rootIdx : Nat),
          Witness bundle roots path rootIdx) →
      Verdict.validateX509Base64 rootsB64 bundleB64 task = .ok true := by
  intro rootsB64 bundleB64 task
  dsimp only
  intro h
  change (∃ path r, Witness (bundleB64.filterMap Verdict.parseX509Base64) (rootsB64.filterMap Verdict.parseX509Base64) path r) at h
  generalize hr : rootsB64.filterMap Verdict.parseX509Base64 = roots at h ⊢
  generalize hb : bundleB64.filterMap Verdict.parseX509Base64 = bundle at h ⊢
  change (∃ path r, Witness bundle roots path r) at h
  obtain ⟨path, r, hne, hhead, hn, hbounds, hr', hedges, hroot⟩ := h
  cases path with
  | nil => contradiction
  | cons current tail =>
    have hc : current = 0 := by simpa using hhead
    subst current
    have hnodup : (0 :: tail).Nodup := by simpa [Verdict.isSimplePath] using hn
    have hbound : ∀ i, i ∈ 0 :: tail → i < bundle.length := by
      intro i hi
      exact of_decide_eq_true ((List.all_eq_true.mp hbounds) i hi)
    have hp : 0 < bundle.length := hbound 0 (by simp)
    have hsub : ∀ i, i ∈ tail → i ∈ (List.range bundle.length).erase 0 := by
      intro i hi
      apply (List.mem_erase_of_ne (by intro heq; subst i; exact (List.nodup_cons.mp hnodup).1 hi)).mpr
      exact List.mem_range.mpr (hbound i (by simp [hi]))
    have hlen : tail.length ≤ bundle.length - 1 := by
      have ht := nodup_subset_length (0 :: tail) (List.range bundle.length) hnodup (by
        intro i hi; exact List.mem_range.mpr (hbound i hi))
      simp only [List.length_cons, List.length_range] at ht
      omega
    have hw : Walk bundle roots 0 tail := (walk_links bundle roots 0 tail).mpr ⟨hedges, r, hr', hroot⟩
    have hs := search_complete bundle roots (bundle.length - 1)
      ((List.range bundle.length).erase 0) 0 tail (List.nodup_cons.mp hnodup).2 hsub hlen hw
    change Verdict.validateX509Base64 rootsB64 bundleB64 task = .ok true
    simp only [Verdict.validateX509Base64, hr, hb]
    simp [List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_length_pos hp), hs]

end VerdictCertificates.Search
