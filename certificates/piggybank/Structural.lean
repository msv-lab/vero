import PiggybankV2.Spec.PiggyBankCorrect
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_receive_dispatch_insert : spec_receive_dispatch_insert canonical := by
  unfold spec_receive_dispatch_insert
  intros
  rfl

#print axioms structural_spec_receive_dispatch_insert

theorem structural_spec_receive_dispatch_smash : spec_receive_dispatch_smash canonical := by
  unfold spec_receive_dispatch_smash
  intros
  rfl

#print axioms structural_spec_receive_dispatch_smash
