import Aesop
import Lean.Elab.Tactic.Omega
import Primefac.Spec.Factor
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_isprime_zero : spec_isprime_zero canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_isprime_zero, canonical, Primefac.isprime, Primefac.iterprod, Primefac.primefac]
  | solve | unfold spec_isprime_zero; dsimp [canonical]; aesop
  | solve | unfold spec_isprime_zero; dsimp [canonical]; intros; omega

#print axioms canonical_spec_isprime_zero

theorem canonical_spec_isprime_one : spec_isprime_one canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_isprime_one, canonical, Primefac.isprime, Primefac.iterprod, Primefac.primefac]
  | solve | unfold spec_isprime_one; dsimp [canonical]; aesop
  | solve | unfold spec_isprime_one; dsimp [canonical]; intros; omega

#print axioms canonical_spec_isprime_one

theorem canonical_spec_isprime_two : spec_isprime_two canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_isprime_two, canonical, Primefac.isprime, Primefac.iterprod, Primefac.primefac]
  | solve | unfold spec_isprime_two; dsimp [canonical]; aesop
  | solve | unfold spec_isprime_two; dsimp [canonical]; intros; omega

#print axioms canonical_spec_isprime_two

theorem canonical_spec_iterprod_nil : spec_iterprod_nil canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_iterprod_nil, canonical, Primefac.isprime, Primefac.iterprod, Primefac.primefac]
  | solve | unfold spec_iterprod_nil; dsimp [canonical]; aesop
  | solve | unfold spec_iterprod_nil; dsimp [canonical]; intros; omega

#print axioms canonical_spec_iterprod_nil

theorem canonical_spec_iterprod_cons : spec_iterprod_cons canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_iterprod_cons, canonical, Primefac.isprime, Primefac.iterprod, Primefac.primefac]
  | solve | unfold spec_iterprod_cons; dsimp [canonical]; aesop
  | solve | unfold spec_iterprod_cons; dsimp [canonical]; intros; omega

#print axioms canonical_spec_iterprod_cons

theorem canonical_spec_primefac_one : spec_primefac_one canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_primefac_one, canonical, Primefac.isprime, Primefac.iterprod, Primefac.primefac]
  | solve | unfold spec_primefac_one; dsimp [canonical]; aesop
  | solve | unfold spec_primefac_one; dsimp [canonical]; intros; omega

#print axioms canonical_spec_primefac_one
