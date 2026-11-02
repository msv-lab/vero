namespace CanonicalAxiomAudit

-- A conditional refutation of the removed placeholder assumption, not a correctness certificate.
theorem unfinished_assumption_false (bad : ∀ (A : Type), A) : False :=
  nomatch bad Empty

#print axioms unfinished_assumption_false

end CanonicalAxiomAudit
