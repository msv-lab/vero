import Difflib.Spec.SequenceMatcher
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_flm_empty_left : spec_flm_empty_left canonical := by
  unfold spec_flm_empty_left
  intros
  rfl

#print axioms structural_spec_flm_empty_left
