import Aesop
import Lean.Elab.Tactic.Omega
import VerifiedIronkv.Spec.CmessageV
import VerifiedIronkv.Spec.DelegationMapV
import VerifiedIronkv.Spec.HostImplV
import VerifiedIronkv.Spec.IoT
import VerifiedIronkv.Spec.KeysT
import VerifiedIronkv.Spec.NetShtV
import VerifiedIronkv.Spec.SeqIsUniqueV
import VerifiedIronkv.Spec.SingleDeliveryModelV
import VerifiedIronkv.Spec.SingleDeliveryStateV
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_clone_l151_preserves_key : spec_clone_l151_preserves_key canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_clone_l151_preserves_key, canonical, Bank.clone_l151, Bank.delegate_for_key_range_is_host_impl, Bank.endpoints_contain, Bank.get, Bank.get_l1102, Bank.is_marshallable, Bank.is_message_marshallable, Bank.maybe_ack_packet_impl, Bank.new_impl, Bank.new_l1053, Bank.range_consistent_impl, Bank.real_init_impl, Bank.receive_ack_impl, Bank.receive_impl, Bank.receive_real_packet_impl, Bank.retransmit_un_acked_packets, Bank.send, Bank.send_single_cmessage, Bank.set_l1115, Bank.should_ack_sigle_message_impl, Bank.sht_demarshall_data_method, Bank.test_unique, Bank.valid_physical_address]
  | solve | unfold spec_clone_l151_preserves_key; dsimp [canonical]; aesop
  | solve | unfold spec_clone_l151_preserves_key; dsimp [canonical]; intros; omega

#print axioms canonical_spec_clone_l151_preserves_key

theorem canonical_spec_is_message_marshallable_matches_model : spec_is_message_marshallable_matches_model canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_is_message_marshallable_matches_model, canonical, Bank.clone_l151, Bank.delegate_for_key_range_is_host_impl, Bank.endpoints_contain, Bank.get, Bank.get_l1102, Bank.is_marshallable, Bank.is_message_marshallable, Bank.maybe_ack_packet_impl, Bank.new_impl, Bank.new_l1053, Bank.range_consistent_impl, Bank.real_init_impl, Bank.receive_ack_impl, Bank.receive_impl, Bank.receive_real_packet_impl, Bank.retransmit_un_acked_packets, Bank.send, Bank.send_single_cmessage, Bank.set_l1115, Bank.should_ack_sigle_message_impl, Bank.sht_demarshall_data_method, Bank.test_unique, Bank.valid_physical_address]
  | solve | unfold spec_is_message_marshallable_matches_model; dsimp [canonical]; aesop
  | solve | unfold spec_is_message_marshallable_matches_model; dsimp [canonical]; intros; omega

#print axioms canonical_spec_is_message_marshallable_matches_model

theorem canonical_spec_is_marshallable_matches_model : spec_is_marshallable_matches_model canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_is_marshallable_matches_model, canonical, Bank.clone_l151, Bank.delegate_for_key_range_is_host_impl, Bank.endpoints_contain, Bank.get, Bank.get_l1102, Bank.is_marshallable, Bank.is_message_marshallable, Bank.maybe_ack_packet_impl, Bank.new_impl, Bank.new_l1053, Bank.range_consistent_impl, Bank.real_init_impl, Bank.receive_ack_impl, Bank.receive_impl, Bank.receive_real_packet_impl, Bank.retransmit_un_acked_packets, Bank.send, Bank.send_single_cmessage, Bank.set_l1115, Bank.should_ack_sigle_message_impl, Bank.sht_demarshall_data_method, Bank.test_unique, Bank.valid_physical_address]
  | solve | unfold spec_is_marshallable_matches_model; dsimp [canonical]; aesop
  | solve | unfold spec_is_marshallable_matches_model; dsimp [canonical]; intros; omega

#print axioms canonical_spec_is_marshallable_matches_model
