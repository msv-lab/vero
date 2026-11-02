import PackagingVersion.Spec.Version
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_max_singleton : spec_max_singleton canonical := by
  unfold spec_max_singleton
  intros
  rfl

#print axioms structural_spec_max_singleton

theorem structural_spec_min_singleton : spec_min_singleton canonical := by
  unfold spec_min_singleton
  intros
  rfl

#print axioms structural_spec_min_singleton
