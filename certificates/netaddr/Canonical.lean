import Aesop
import Lean.Elab.Tactic.Omega
import Netaddr.Spec.Cidr
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_network_addr_aligned : spec_network_addr_aligned canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_network_addr_aligned, canonical, Netaddr.broadcast, Netaddr.containsAddr, Netaddr.iprangeToCidrs, Netaddr.networkAddr, Netaddr.spanningCidr]
  | solve | unfold spec_network_addr_aligned; dsimp [canonical]; aesop
  | solve | unfold spec_network_addr_aligned; dsimp [canonical]; intros; omega

#print axioms canonical_spec_network_addr_aligned

theorem canonical_spec_spanning_empty : spec_spanning_empty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_spanning_empty, canonical, Netaddr.broadcast, Netaddr.containsAddr, Netaddr.iprangeToCidrs, Netaddr.networkAddr, Netaddr.spanningCidr]
  | solve | unfold spec_spanning_empty; dsimp [canonical]; aesop
  | solve | unfold spec_spanning_empty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_spanning_empty
