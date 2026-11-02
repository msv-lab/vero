import DepositSc.Spec.Bits
import DepositSc.Spec.Contract
import DepositSc.Spec.Merkle
import DepositSc.Spec.Tree
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_power2 : spec_power2 canonical := by
  unfold spec_power2
  intros
  rfl

#print axioms structural_spec_power2

theorem structural_spec_default_value_zero : spec_default_value_zero canonical := by
  unfold spec_default_value_zero
  intros
  rfl

#print axioms structural_spec_default_value_zero

theorem structural_spec_default_value_succ : spec_default_value_succ canonical := by
  unfold spec_default_value_succ
  intros
  rfl

#print axioms structural_spec_default_value_succ

theorem structural_spec_node_at_nil : spec_node_at_nil canonical := by
  unfold spec_node_at_nil
  intros
  rfl

#print axioms structural_spec_node_at_nil

theorem structural_spec_node_at_cons : spec_node_at_cons canonical := by
  unfold spec_node_at_cons
  intros
  rfl

#print axioms structural_spec_node_at_cons

theorem structural_spec_sibling_value_at_zero : spec_sibling_value_at_zero canonical := by
  unfold spec_sibling_value_at_zero
  intros
  rfl

#print axioms structural_spec_sibling_value_at_zero

theorem structural_spec_height_leaf : spec_height_leaf canonical := by
  unfold spec_height_leaf
  intros
  rfl

#print axioms structural_spec_height_leaf

theorem structural_spec_height_node : spec_height_node canonical := by
  unfold spec_height_node
  intros
  rfl

#print axioms structural_spec_height_node

theorem structural_spec_leaves_in_leaf : spec_leaves_in_leaf canonical := by
  unfold spec_leaves_in_leaf
  intros
  rfl

#print axioms structural_spec_leaves_in_leaf

theorem structural_spec_leaves_in_node : spec_leaves_in_node canonical := by
  unfold spec_leaves_in_node
  intros
  rfl

#print axioms structural_spec_leaves_in_node

theorem structural_spec_node_at_root : spec_node_at_root canonical := by
  unfold spec_node_at_root
  intros
  rfl

#print axioms structural_spec_node_at_root
