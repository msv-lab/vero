import Verdict.Spec.Validator

namespace VerdictCertificates.Validator

theorem simplePath_noDuplicate :
  ∀ (path : Verdict.BundlePath) (i : Nat),
      path.count i ≥ 2 →
      Verdict.isSimplePath path = false := by
  intro path i hc
  simp only [Verdict.isSimplePath, decide_eq_false_iff_not]
  intro hn
  have := List.nodup_iff_count.mp hn i
  omega

theorem simplePath_tail :
  ∀ (i : Nat) (path : Verdict.BundlePath),
      Verdict.isSimplePath (i :: path) = true →
      Verdict.isSimplePath path = true := by
  intro i path h
  simp only [Verdict.isSimplePath, decide_eq_true_eq] at *
  exact (List.nodup_cons.mp h).2

private theorem filterMap_getElem_length (bundle : List Verdict.Certificate) (path : List Nat)
    (h : ∀ i, i ∈ path → i < bundle.length) :
    (path.filterMap (fun i => bundle[i]?)).length = path.length := by
  induction path with
  | nil => rfl
  | cons i path ih =>
    have hi := h i (by simp)
    simp only [List.filterMap_cons, List.getElem?_eq_getElem hi, List.length_cons]
    exact congrArg (· + 1) (ih (fun j hj => h j (by simp [hj])))

theorem chainFromPath_shape :
  ∀ (bundle : List Verdict.Certificate)
      (path : Verdict.BundlePath)
      (root : Verdict.Certificate),
      Verdict.pathInBounds path bundle.length = true →
      let chain := Verdict.chainFromPath bundle path root
      chain.length = path.length + 1 ∧ chain.getLast? = some root := by
  intro bundle path root h
  have hb : ∀ i, i ∈ path → i < bundle.length := by
    intro i hi
    exact of_decide_eq_true ((List.all_eq_true.mp h) i hi)
  constructor
  · simp [Verdict.chainFromPath, filterMap_getElem_length bundle path hb]
  · simp [Verdict.chainFromPath]

theorem chainFromPath_head :
  ∀ (bundle : List Verdict.Certificate)
      (i : Nat) (path : Verdict.BundlePath)
      (root : Verdict.Certificate),
      Verdict.pathInBounds (i :: path) bundle.length = true →
      (Verdict.chainFromPath bundle (i :: path) root).head?
        = bundle[i]? := by
  intro bundle i path root h
  have hi : i < bundle.length := by
    exact of_decide_eq_true ((List.all_eq_true.mp h) i (by simp))
  simp [Verdict.chainFromPath, List.getElem?_eq_getElem hi]

end VerdictCertificates.Validator
