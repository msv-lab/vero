import ToposortSort.Spec.Toposort

set_option maxHeartbeats 2000

theorem manual_spec_flatten_failure_consistency : spec_flatten_failure_consistency canonical := by
  intro data sort
  change Toposort.toposort data = none ↔ Toposort.toposort_flatten data sort = none
  unfold Toposort.toposort_flatten
  cases Toposort.toposort data <;> simp

#print axioms manual_spec_flatten_failure_consistency

theorem manual_spec_flatten_matches_layered_output_sorted : spec_flatten_matches_layered_output_sorted canonical := by
  intro data layers h
  change Toposort.toposort data = some layers at h
  change Toposort.toposort_flatten data true = some (flattenLayersSorted layers)
  simp [Toposort.toposort_flatten, h, flattenLayersSorted]

#print axioms manual_spec_flatten_matches_layered_output_sorted

theorem manual_spec_flatten_matches_layered_output_unsorted : spec_flatten_matches_layered_output_unsorted canonical := by
  intro data layers h
  change Toposort.toposort data = some layers at h
  change Toposort.toposort_flatten data false = some (flattenLayersUnsorted layers)
  simp [Toposort.toposort_flatten, h, flattenLayersUnsorted]

#print axioms manual_spec_flatten_matches_layered_output_unsorted
