import Cachetools.Spec.Lru
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_capacity_preserved : spec_capacity_preserved canonical := by
  unfold spec_capacity_preserved
  intros
  rfl

#print axioms structural_spec_capacity_preserved

theorem structural_spec_put_order_exact : spec_put_order_exact canonical := by
  unfold spec_put_order_exact
  intros
  rfl

#print axioms structural_spec_put_order_exact
