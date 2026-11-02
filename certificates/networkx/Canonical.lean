import Aesop
import Lean.Elab.Tactic.Omega
import Networkx.Spec.Components
import Networkx.Spec.Mst
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_component_of_mem_iff : spec_component_of_mem_iff canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_component_of_mem_iff, canonical, Networkx.componentOf, Networkx.mstWeight, Networkx.numConnectedComponents, Networkx.numTreeEdges, Networkx.sameComponent, Networkx.subsetWeight]
  | solve | unfold spec_component_of_mem_iff; dsimp [canonical]; aesop
  | solve | unfold spec_component_of_mem_iff; dsimp [canonical]; intros; omega

#print axioms canonical_spec_component_of_mem_iff

theorem canonical_spec_mst_empty : spec_mst_empty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_mst_empty, canonical, Networkx.componentOf, Networkx.mstWeight, Networkx.numConnectedComponents, Networkx.numTreeEdges, Networkx.sameComponent, Networkx.subsetWeight]
  | solve | unfold spec_mst_empty; dsimp [canonical]; aesop
  | solve | unfold spec_mst_empty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_mst_empty

theorem canonical_spec_subset_weight_nil : spec_subset_weight_nil canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_subset_weight_nil, canonical, Networkx.componentOf, Networkx.mstWeight, Networkx.numConnectedComponents, Networkx.numTreeEdges, Networkx.sameComponent, Networkx.subsetWeight]
  | solve | unfold spec_subset_weight_nil; dsimp [canonical]; aesop
  | solve | unfold spec_subset_weight_nil; dsimp [canonical]; intros; omega

#print axioms canonical_spec_subset_weight_nil
