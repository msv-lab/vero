import Aesop
import Lean.Elab.Tactic.Omega
import PiggybankV2.Spec.PiggyBankCorrect
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_insert_negative_amount_fails : spec_insert_negative_amount_fails canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_insert_negative_amount_fails, canonical, PiggybankV2.init, PiggybankV2.insert, PiggybankV2.receive, PiggybankV2.smash]
  | solve | unfold spec_insert_negative_amount_fails; dsimp [canonical]; aesop
  | solve | unfold spec_insert_negative_amount_fails; dsimp [canonical]; intros; omega

#print axioms canonical_spec_insert_negative_amount_fails

theorem canonical_spec_receive_missing_msg_fails : spec_receive_missing_msg_fails canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_receive_missing_msg_fails, canonical, PiggybankV2.init, PiggybankV2.insert, PiggybankV2.receive, PiggybankV2.smash]
  | solve | unfold spec_receive_missing_msg_fails; dsimp [canonical]; aesop
  | solve | unfold spec_receive_missing_msg_fails; dsimp [canonical]; intros; omega

#print axioms canonical_spec_receive_missing_msg_fails

theorem canonical_spec_initializes_correctly : spec_initializes_correctly canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_initializes_correctly, canonical, PiggybankV2.init, PiggybankV2.insert, PiggybankV2.receive, PiggybankV2.smash]
  | solve | unfold spec_initializes_correctly; dsimp [canonical]; aesop
  | solve | unfold spec_initializes_correctly; dsimp [canonical]; intros; omega

#print axioms canonical_spec_initializes_correctly

theorem canonical_spec_initializes_owner_and_balance : spec_initializes_owner_and_balance canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_initializes_owner_and_balance, canonical, PiggybankV2.init, PiggybankV2.insert, PiggybankV2.receive, PiggybankV2.smash]
  | solve | unfold spec_initializes_owner_and_balance; dsimp [canonical]; aesop
  | solve | unfold spec_initializes_owner_and_balance; dsimp [canonical]; intros; omega

#print axioms canonical_spec_initializes_owner_and_balance
