import Aesop
import Lean.Elab.Tactic.Omega
import Rsa.Spec.Common
import Rsa.Spec.Transform
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_encrypt_int_correct : spec_encrypt_int_correct canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_encrypt_int_correct, canonical, Rsa.crt, Rsa.decryptInt, Rsa.encryptInt, Rsa.extendedGcd, Rsa.gcd, Rsa.inverse]
  | solve | unfold spec_encrypt_int_correct; dsimp [canonical]; aesop
  | solve | unfold spec_encrypt_int_correct; dsimp [canonical]; intros; omega

#print axioms canonical_spec_encrypt_int_correct

theorem canonical_spec_decrypt_int_correct : spec_decrypt_int_correct canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_decrypt_int_correct, canonical, Rsa.crt, Rsa.decryptInt, Rsa.encryptInt, Rsa.extendedGcd, Rsa.gcd, Rsa.inverse]
  | solve | unfold spec_decrypt_int_correct; dsimp [canonical]; aesop
  | solve | unfold spec_decrypt_int_correct; dsimp [canonical]; intros; omega

#print axioms canonical_spec_decrypt_int_correct

theorem canonical_spec_encrypt_exp_one : spec_encrypt_exp_one canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_encrypt_exp_one, canonical, Rsa.crt, Rsa.decryptInt, Rsa.encryptInt, Rsa.extendedGcd, Rsa.gcd, Rsa.inverse]
  | solve | unfold spec_encrypt_exp_one; dsimp [canonical]; aesop
  | solve | unfold spec_encrypt_exp_one; dsimp [canonical]; intros; omega

#print axioms canonical_spec_encrypt_exp_one

theorem canonical_spec_encrypt_vec : spec_encrypt_vec canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_encrypt_vec, canonical, Rsa.crt, Rsa.decryptInt, Rsa.encryptInt, Rsa.extendedGcd, Rsa.gcd, Rsa.inverse]
  | solve | unfold spec_encrypt_vec; dsimp [canonical]; aesop
  | solve | unfold spec_encrypt_vec; dsimp [canonical]; intros; omega

#print axioms canonical_spec_encrypt_vec

theorem canonical_spec_gcd_zero_right : spec_gcd_zero_right canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_gcd_zero_right, canonical, Rsa.crt, Rsa.decryptInt, Rsa.encryptInt, Rsa.extendedGcd, Rsa.gcd, Rsa.inverse]
  | solve | unfold spec_gcd_zero_right; dsimp [canonical]; aesop
  | solve | unfold spec_gcd_zero_right; dsimp [canonical]; intros; omega

#print axioms canonical_spec_gcd_zero_right

theorem canonical_spec_gcd_vec : spec_gcd_vec canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_gcd_vec, canonical, Rsa.crt, Rsa.decryptInt, Rsa.encryptInt, Rsa.extendedGcd, Rsa.gcd, Rsa.inverse]
  | solve | unfold spec_gcd_vec; dsimp [canonical]; aesop
  | solve | unfold spec_gcd_vec; dsimp [canonical]; intros; omega

#print axioms canonical_spec_gcd_vec

theorem canonical_spec_extended_gcd_vec1 : spec_extended_gcd_vec1 canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_extended_gcd_vec1, canonical, Rsa.crt, Rsa.decryptInt, Rsa.encryptInt, Rsa.extendedGcd, Rsa.gcd, Rsa.inverse]
  | solve | unfold spec_extended_gcd_vec1; dsimp [canonical]; aesop
  | solve | unfold spec_extended_gcd_vec1; dsimp [canonical]; intros; omega

#print axioms canonical_spec_extended_gcd_vec1

theorem canonical_spec_extended_gcd_vec2 : spec_extended_gcd_vec2 canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_extended_gcd_vec2, canonical, Rsa.crt, Rsa.decryptInt, Rsa.encryptInt, Rsa.extendedGcd, Rsa.gcd, Rsa.inverse]
  | solve | unfold spec_extended_gcd_vec2; dsimp [canonical]; aesop
  | solve | unfold spec_extended_gcd_vec2; dsimp [canonical]; intros; omega

#print axioms canonical_spec_extended_gcd_vec2

theorem canonical_spec_inverse_vec1 : spec_inverse_vec1 canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_inverse_vec1, canonical, Rsa.crt, Rsa.decryptInt, Rsa.encryptInt, Rsa.extendedGcd, Rsa.gcd, Rsa.inverse]
  | solve | unfold spec_inverse_vec1; dsimp [canonical]; aesop
  | solve | unfold spec_inverse_vec1; dsimp [canonical]; intros; omega

#print axioms canonical_spec_inverse_vec1

theorem canonical_spec_inverse_vec2 : spec_inverse_vec2 canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_inverse_vec2, canonical, Rsa.crt, Rsa.decryptInt, Rsa.encryptInt, Rsa.extendedGcd, Rsa.gcd, Rsa.inverse]
  | solve | unfold spec_inverse_vec2; dsimp [canonical]; aesop
  | solve | unfold spec_inverse_vec2; dsimp [canonical]; intros; omega

#print axioms canonical_spec_inverse_vec2

theorem canonical_spec_crt_vec1 : spec_crt_vec1 canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_crt_vec1, canonical, Rsa.crt, Rsa.decryptInt, Rsa.encryptInt, Rsa.extendedGcd, Rsa.gcd, Rsa.inverse]
  | solve | unfold spec_crt_vec1; dsimp [canonical]; aesop
  | solve | unfold spec_crt_vec1; dsimp [canonical]; intros; omega

#print axioms canonical_spec_crt_vec1

theorem canonical_spec_crt_vec2 : spec_crt_vec2 canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_crt_vec2, canonical, Rsa.crt, Rsa.decryptInt, Rsa.encryptInt, Rsa.extendedGcd, Rsa.gcd, Rsa.inverse]
  | solve | unfold spec_crt_vec2; dsimp [canonical]; aesop
  | solve | unfold spec_crt_vec2; dsimp [canonical]; intros; omega

#print axioms canonical_spec_crt_vec2
