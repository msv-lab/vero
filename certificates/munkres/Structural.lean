import Munkres.Spec.Assign
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_assignmentCost_fold : spec_assignmentCost_fold canonical := by
  unfold spec_assignmentCost_fold
  intros
  rfl

#print axioms structural_spec_assignmentCost_fold
