import Croniter.Spec.Cron
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_cronMatches_iff : spec_cronMatches_iff canonical := by
  unfold spec_cronMatches_iff
  intros
  rfl

#print axioms structural_spec_cronMatches_iff
