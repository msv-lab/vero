import Aesop
import Lean.Elab.Tactic.Omega
import Ipaddress.Spec.Cidr
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_collapse_subset : spec_collapse_subset canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_collapse_subset, canonical, Ipaddress.broadcast, Ipaddress.collapse, Ipaddress.containsAddr, Ipaddress.networkAddr, Ipaddress.supernet]
  | solve | unfold spec_collapse_subset; dsimp [canonical]; aesop
  | solve | unfold spec_collapse_subset; dsimp [canonical]; intros; omega

#print axioms canonical_spec_collapse_subset

theorem canonical_spec_network_addr_aligned : spec_network_addr_aligned canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_network_addr_aligned, canonical, Ipaddress.broadcast, Ipaddress.collapse, Ipaddress.containsAddr, Ipaddress.networkAddr, Ipaddress.supernet]
  | solve | unfold spec_network_addr_aligned; dsimp [canonical]; aesop
  | solve | unfold spec_network_addr_aligned; dsimp [canonical]; intros; omega

#print axioms canonical_spec_network_addr_aligned

theorem canonical_spec_contains_self_network : spec_contains_self_network canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_contains_self_network, canonical, Ipaddress.broadcast, Ipaddress.collapse, Ipaddress.containsAddr, Ipaddress.networkAddr, Ipaddress.supernet]
  | solve | unfold spec_contains_self_network; dsimp [canonical]; aesop
  | solve | unfold spec_contains_self_network; dsimp [canonical]; intros; omega

#print axioms canonical_spec_contains_self_network

theorem canonical_spec_supernet_prefix : spec_supernet_prefix canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_supernet_prefix, canonical, Ipaddress.broadcast, Ipaddress.collapse, Ipaddress.containsAddr, Ipaddress.networkAddr, Ipaddress.supernet]
  | solve | unfold spec_supernet_prefix; dsimp [canonical]; aesop
  | solve | unfold spec_supernet_prefix; dsimp [canonical]; intros; omega

#print axioms canonical_spec_supernet_prefix

theorem canonical_spec_collapse_nil : spec_collapse_nil canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_collapse_nil, canonical, Ipaddress.broadcast, Ipaddress.collapse, Ipaddress.containsAddr, Ipaddress.networkAddr, Ipaddress.supernet]
  | solve | unfold spec_collapse_nil; dsimp [canonical]; aesop
  | solve | unfold spec_collapse_nil; dsimp [canonical]; intros; omega

#print axioms canonical_spec_collapse_nil

theorem canonical_spec_collapse_wf : spec_collapse_wf canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_collapse_wf, canonical, Ipaddress.broadcast, Ipaddress.collapse, Ipaddress.containsAddr, Ipaddress.networkAddr, Ipaddress.supernet]
  | solve | unfold spec_collapse_wf; dsimp [canonical]; aesop
  | solve | unfold spec_collapse_wf; dsimp [canonical]; intros; omega

#print axioms canonical_spec_collapse_wf
