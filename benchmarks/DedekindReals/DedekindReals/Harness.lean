import DedekindReals.Bundle

open DedekindReals

structure RepoImpl where
  dedekindReals : DedekindRealsBundle

def DedekindReals.canonicalDedekindReals : DedekindRealsBundle where
  Rlt := Rlt
  Rle := Rle
  Req := Req
  Rneq := Rneq
  R_of_Q := R_of_Q
  Rzero := Rzero
  Zone := Zone
  Rplus := Rplus
  Ropp := Ropp
  Rminus := Rminus
  CauchyQ_R := CauchyQ_R
  RCut_of_R := RCut_of_R
  R_of_RCut := R_of_RCut
  Rmult := Rmult
  Rinv := Rinv
  Rmin := Rmin
  Rmax := Rmax

def canonical : RepoImpl where
  dedekindReals := canonicalDedekindReals

namespace DedekindReals

syntax "joint_unsat" : tactic

macro_rules
  | `(tactic| joint_unsat) => `(tactic| first | contradiction | simp_all)

end DedekindReals

syntax "joint_unsat" ident ident ident* "by" tacticSeq : command

open Lean in
macro_rules
  | `(joint_unsat $s1 $s2 $[$rest]* by $proof) => do
    let specs := #[s1, s2] ++ rest
    let name := specs.foldl (init := `joint_unsat) fun acc s => Name.append acc s.getId
    let mut body ← `($(specs[0]!) impl)
    for s in specs[1:] do
      body ← `($body ∧ $s impl)
    `(theorem $(mkIdent name) : ¬ ∃ impl : RepoImpl, $body := by $proof)
