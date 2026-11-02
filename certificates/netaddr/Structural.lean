import Netaddr.Spec.Cidr
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_broadcast_eq : spec_broadcast_eq canonical := by
  unfold spec_broadcast_eq
  intros
  rfl

#print axioms structural_spec_broadcast_eq
