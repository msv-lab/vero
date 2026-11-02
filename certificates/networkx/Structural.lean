import Networkx.Spec.Components
import Networkx.Spec.Mst
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_num_components_eq_classes : spec_num_components_eq_classes canonical := by
  unfold spec_num_components_eq_classes
  intros
  rfl

#print axioms structural_spec_num_components_eq_classes

theorem structural_spec_subset_weight_correct : spec_subset_weight_correct canonical := by
  unfold spec_subset_weight_correct
  intros
  rfl

#print axioms structural_spec_subset_weight_correct
