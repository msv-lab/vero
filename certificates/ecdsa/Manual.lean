import Lean.Elab.Tactic.Omega
import Ecdsa.Spec.Modular

set_option maxHeartbeats 5000

private theorem findSqrt_witness (a p n r : Nat) (hr : r ≤ n) (hs : (r * r) % p = a % p) :
    ∃ x, findSqrt a p n = some x ∧ r ≤ x := by
  induction n with
  | zero =>
    have er : r = 0 := by omega
    subst r
    exact ⟨0, by simp [findSqrt, hs], by omega⟩
  | succ n ih =>
    by_cases ht : ((n + 1) * (n + 1)) % p = a % p
    · exact ⟨n + 1, by simp [findSqrt, ht], hr⟩
    · have hrn : r ≤ n := by
        have hne : r ≠ n + 1 := by intro he; subst r; exact ht hs
        omega
      obtain ⟨x, hx, hge⟩ := ih hrn
      exact ⟨x, by simp [findSqrt, ht, hx], hge⟩

private theorem findSqrt_sound (a p n x : Nat) (h : findSqrt a p n = some x) :
    x ≤ n ∧ (x * x) % p = a % p := by
  induction n with
  | zero =>
    by_cases ht : (0 * 0) % p = a % p
    · simp [findSqrt, ht] at h
      subst x
      exact ⟨by omega, ht⟩
    · simp [findSqrt, ht] at h
      exact False.elim (ht (by simpa using h.1))
  | succ n ih =>
    by_cases ht : ((n + 1) * (n + 1)) % p = a % p
    · simp [findSqrt, ht] at h
      subst x
      exact ⟨by omega, ht⟩
    · have h' : findSqrt a p n = some x := by simpa [findSqrt, ht] using h
      have hx := ih h'
      exact ⟨by omega, hx.2⟩

theorem manual_spec_sqrt_mod_prime_greatest_root : spec_sqrt_mod_prime_greatest_root canonical := by
  intro a p r hr hs
  obtain ⟨x, hx, hge⟩ := findSqrt_witness a p p r hr hs
  simpa [canonical, Ecdsa.sqrtModPrime, hx] using hge
#print axioms manual_spec_sqrt_mod_prime_greatest_root

theorem manual_spec_sqrt_mod_prime_squares_back_general : spec_sqrt_mod_prime_squares_back_general canonical := by
  intro a p _hex hroot
  obtain ⟨r, hr, hs⟩ := hroot
  obtain ⟨x, hx, _⟩ := findSqrt_witness a p p r (by omega) hs
  have hs' := (findSqrt_sound a p p x hx).2
  simpa [canonical, Ecdsa.sqrtModPrime, hx] using hs'
#print axioms manual_spec_sqrt_mod_prime_squares_back_general

theorem manual_spec_sqrt_mod_prime_nonzero_range : spec_sqrt_mod_prime_nonzero_range canonical := by
  intro a p hp hn
  change (findSqrt a p p).getD 0 < p
  cases he : findSqrt a p p with
  | none => simpa using hp
  | some x =>
    have hs := findSqrt_sound a p p x he
    have hne : x ≠ p := by
      intro hx
      subst x
      have hz : (p * p) % p = 0 := by simp
      exact hn (hs.2.symm.trans hz)
    simp only [Option.getD_some]
    omega
#print axioms manual_spec_sqrt_mod_prime_nonzero_range

theorem manual_spec_jacobi_denom_one : spec_jacobi_denom_one canonical := by
  intro a
  simp [canonical, Ecdsa.jacobi]
#print axioms manual_spec_jacobi_denom_one
