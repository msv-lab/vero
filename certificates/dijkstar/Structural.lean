import Dijkstar.Spec.ShortestPath
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_edge_weight_correct : spec_edge_weight_correct canonical := by
  unfold spec_edge_weight_correct
  intros
  rfl

#print axioms structural_spec_edge_weight_correct
