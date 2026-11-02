import Aesop
import Lean.Elab.Tactic.Omega
import Reedsolo.Spec.Field
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_gf_pow_succ : spec_gf_pow_succ canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_gf_pow_succ, canonical, Reedsolo.gfInverse, Reedsolo.gfMul, Reedsolo.gfPow, Reedsolo.rsEncodeMsg, Reedsolo.rsGeneratorPoly]
  | solve | unfold spec_gf_pow_succ; dsimp [canonical]; aesop
  | solve | unfold spec_gf_pow_succ; dsimp [canonical]; intros; omega

#print axioms canonical_spec_gf_pow_succ

theorem canonical_spec_generator_poly_base : spec_generator_poly_base canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_generator_poly_base, canonical, Reedsolo.gfInverse, Reedsolo.gfMul, Reedsolo.gfPow, Reedsolo.rsEncodeMsg, Reedsolo.rsGeneratorPoly]
  | solve | unfold spec_generator_poly_base; dsimp [canonical]; aesop
  | solve | unfold spec_generator_poly_base; dsimp [canonical]; intros; omega

#print axioms canonical_spec_generator_poly_base

theorem canonical_spec_encode_systematic : spec_encode_systematic canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_encode_systematic, canonical, Reedsolo.gfInverse, Reedsolo.gfMul, Reedsolo.gfPow, Reedsolo.rsEncodeMsg, Reedsolo.rsGeneratorPoly]
  | solve | unfold spec_encode_systematic; dsimp [canonical]; aesop
  | solve | unfold spec_encode_systematic; dsimp [canonical]; intros; omega

#print axioms canonical_spec_encode_systematic
