import ArithmeticV2.Spec.DivMod
import ArithmeticV2.Spec.Logarithm
import ArithmeticV2.Spec.Mul
import ArithmeticV2.Spec.Overflow
import ArithmeticV2.Spec.Power
import ArithmeticV2.Spec.Power2
import ArithmeticV2.Spec.Internals.DivInternals
import ArithmeticV2.Spec.Internals.DivInternalsNonlinear
import ArithmeticV2.Spec.Internals.GeneralInternals
import ArithmeticV2.Spec.Internals.ModInternals
import ArithmeticV2.Spec.Internals.ModInternalsNonlinear
import ArithmeticV2.Spec.Internals.MulInternals
import ArithmeticV2.Spec.Internals.MulInternalsNonlinear
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Dedup
import Aesop
set_option maxErrors 1000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000
set_option maxHeartbeats 30000
open ArithmeticV2
namespace ArithmeticCertificates

theorem spec_lemma_div_is_div_recursive : _root_.spec_lemma_div_is_div_recursive canonical := by
  unfold _root_.spec_lemma_div_is_div_recursive
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.div_recursive]); done)
  | ((try simp_all [canonical, ArithmeticV2.div_recursive]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.div_recursive]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.div_recursive]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.div_recursive]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.div_recursive]); grind; done)

theorem spec_lemma_div_by_self : _root_.spec_lemma_div_by_self canonical := by
  unfold _root_.spec_lemma_div_by_self
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_div_of0 : _root_.spec_lemma_div_of0 canonical := by
  unfold _root_.spec_lemma_div_of0
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mod_is_mod_recursive : _root_.spec_lemma_mod_is_mod_recursive canonical := by
  unfold _root_.spec_lemma_mod_is_mod_recursive
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.mod_recursive]); done)
  | ((try simp_all [canonical, ArithmeticV2.mod_recursive]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.mod_recursive]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.mod_recursive]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.mod_recursive]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.mod_recursive]); grind; done)

theorem spec_lemma_mod_self_0 : _root_.spec_lemma_mod_self_0 canonical := by
  unfold _root_.spec_lemma_mod_self_0
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mod_twice : _root_.spec_lemma_mod_twice canonical := by
  unfold _root_.spec_lemma_mod_twice
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mod_multiples_basic : _root_.spec_lemma_mod_multiples_basic canonical := by
  unfold _root_.spec_lemma_mod_multiples_basic
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mod_add_multiples_vanish : _root_.spec_lemma_mod_add_multiples_vanish canonical := by
  unfold _root_.spec_lemma_mod_add_multiples_vanish
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mod_sub_multiples_vanish : _root_.spec_lemma_mod_sub_multiples_vanish canonical := by
  unfold _root_.spec_lemma_mod_sub_multiples_vanish
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mod_multiples_vanish : _root_.spec_lemma_mod_multiples_vanish canonical := by
  unfold _root_.spec_lemma_mod_multiples_vanish
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_add_mod_noop : _root_.spec_lemma_add_mod_noop canonical := by
  unfold _root_.spec_lemma_add_mod_noop
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_add_mod_noop_right : _root_.spec_lemma_add_mod_noop_right canonical := by
  unfold _root_.spec_lemma_add_mod_noop_right
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_sub_mod_noop : _root_.spec_lemma_sub_mod_noop canonical := by
  unfold _root_.spec_lemma_sub_mod_noop
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_sub_mod_noop_right : _root_.spec_lemma_sub_mod_noop_right canonical := by
  unfold _root_.spec_lemma_sub_mod_noop_right
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_div_basics : _root_.spec_lemma_div_basics canonical := by
  unfold _root_.spec_lemma_div_basics
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_div_basics_1 : _root_.spec_lemma_div_basics_1 canonical := by
  unfold _root_.spec_lemma_div_basics_1
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_div_basics_2 : _root_.spec_lemma_div_basics_2 canonical := by
  unfold _root_.spec_lemma_div_basics_2
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_div_basics_3 : _root_.spec_lemma_div_basics_3 canonical := by
  unfold _root_.spec_lemma_div_basics_3
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mod_mod : _root_.spec_lemma_mod_mod canonical := by
  unfold _root_.spec_lemma_mod_mod
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_truncate_middle : _root_.spec_lemma_truncate_middle canonical := by
  unfold _root_.spec_lemma_truncate_middle
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_div_multiples_vanish_quotient : _root_.spec_lemma_div_multiples_vanish_quotient canonical := by
  unfold _root_.spec_lemma_div_multiples_vanish_quotient
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_log0 : _root_.spec_lemma_log0 canonical := by
  unfold _root_.spec_lemma_log0
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.log, ArithmeticV2.logFuel, ArithmeticV2.pow]); done)
  | ((try simp_all [canonical, ArithmeticV2.log, ArithmeticV2.logFuel, ArithmeticV2.pow]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.log, ArithmeticV2.logFuel, ArithmeticV2.pow]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.log, ArithmeticV2.logFuel, ArithmeticV2.pow]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.log, ArithmeticV2.logFuel, ArithmeticV2.pow]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.log, ArithmeticV2.logFuel, ArithmeticV2.pow]); grind; done)

theorem spec_lemma_mul_is_mul_pos : _root_.spec_lemma_mul_is_mul_pos canonical := by
  unfold _root_.spec_lemma_mul_is_mul_pos
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.mul_pos]); done)
  | ((try simp_all [canonical, ArithmeticV2.mul_pos]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.mul_pos]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.mul_pos]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.mul_pos]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.mul_pos]); grind; done)

theorem spec_lemma_mul_basics : _root_.spec_lemma_mul_basics canonical := by
  unfold _root_.spec_lemma_mul_basics
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_basics_1 : _root_.spec_lemma_mul_basics_1 canonical := by
  unfold _root_.spec_lemma_mul_basics_1
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_basics_2 : _root_.spec_lemma_mul_basics_2 canonical := by
  unfold _root_.spec_lemma_mul_basics_2
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_basics_3 : _root_.spec_lemma_mul_basics_3 canonical := by
  unfold _root_.spec_lemma_mul_basics_3
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_basics_4 : _root_.spec_lemma_mul_basics_4 canonical := by
  unfold _root_.spec_lemma_mul_basics_4
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_nonzero : _root_.spec_lemma_mul_nonzero canonical := by
  unfold _root_.spec_lemma_mul_nonzero
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_is_associative : _root_.spec_lemma_mul_is_associative canonical := by
  unfold _root_.spec_lemma_mul_is_associative
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_is_commutative : _root_.spec_lemma_mul_is_commutative canonical := by
  unfold _root_.spec_lemma_mul_is_commutative
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_inequality : _root_.spec_lemma_mul_inequality canonical := by
  unfold _root_.spec_lemma_mul_inequality
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_strict_inequality : _root_.spec_lemma_mul_strict_inequality canonical := by
  unfold _root_.spec_lemma_mul_strict_inequality
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_left_inequality : _root_.spec_lemma_mul_left_inequality canonical := by
  unfold _root_.spec_lemma_mul_left_inequality
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_equality_converse : _root_.spec_lemma_mul_equality_converse canonical := by
  unfold _root_.spec_lemma_mul_equality_converse
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_inequality_converse : _root_.spec_lemma_mul_inequality_converse canonical := by
  unfold _root_.spec_lemma_mul_inequality_converse
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_strict_inequality_converse : _root_.spec_lemma_mul_strict_inequality_converse canonical := by
  unfold _root_.spec_lemma_mul_strict_inequality_converse
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_is_distributive_add : _root_.spec_lemma_mul_is_distributive_add canonical := by
  unfold _root_.spec_lemma_mul_is_distributive_add
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_is_distributive_add_other_way : _root_.spec_lemma_mul_is_distributive_add_other_way canonical := by
  unfold _root_.spec_lemma_mul_is_distributive_add_other_way
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_is_distributive_sub : _root_.spec_lemma_mul_is_distributive_sub canonical := by
  unfold _root_.spec_lemma_mul_is_distributive_sub
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_strictly_positive : _root_.spec_lemma_mul_strictly_positive canonical := by
  unfold _root_.spec_lemma_mul_strictly_positive
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_strictly_increases : _root_.spec_lemma_mul_strictly_increases canonical := by
  unfold _root_.spec_lemma_mul_strictly_increases
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_increases : _root_.spec_lemma_mul_increases canonical := by
  unfold _root_.spec_lemma_mul_increases
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_nonnegative : _root_.spec_lemma_mul_nonnegative canonical := by
  unfold _root_.spec_lemma_mul_nonnegative
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_unary_negation : _root_.spec_lemma_mul_unary_negation canonical := by
  unfold _root_.spec_lemma_mul_unary_negation
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_cancels_negatives : _root_.spec_lemma_mul_cancels_negatives canonical := by
  unfold _root_.spec_lemma_mul_cancels_negatives
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_is_mul_recursive : _root_.spec_lemma_mul_is_mul_recursive canonical := by
  unfold _root_.spec_lemma_mul_is_mul_recursive
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.mul_pos, ArithmeticV2.mul_recursive]); done)
  | ((try simp_all [canonical, ArithmeticV2.mul_pos, ArithmeticV2.mul_recursive]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.mul_pos, ArithmeticV2.mul_recursive]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.mul_pos, ArithmeticV2.mul_recursive]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.mul_pos, ArithmeticV2.mul_recursive]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.mul_pos, ArithmeticV2.mul_recursive]); grind; done)

theorem spec_lemma_mul_by_zero_is_zero : _root_.spec_lemma_mul_by_zero_is_zero canonical := by
  unfold _root_.spec_lemma_mul_by_zero_is_zero
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_upper_bound : _root_.spec_lemma_mul_upper_bound canonical := by
  unfold _root_.spec_lemma_mul_upper_bound
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_strict_upper_bound : _root_.spec_lemma_mul_strict_upper_bound canonical := by
  unfold _root_.spec_lemma_mul_strict_upper_bound
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_lemma_mul_is_distributive_sub_other_way : _root_.spec_lemma_mul_is_distributive_sub_other_way canonical := by
  unfold _root_.spec_lemma_mul_is_distributive_sub_other_way
  intros
  first
  | rfl
  | ((try simp_all [canonical]); done)
  | ((try simp_all [canonical]); omega; done)
  | ((try simp_all [canonical]); aesop; done)
  | ((try simp_all [canonical]); ring; done)
  | ((try simp_all [canonical]); nlinarith; done)
  | ((try simp_all [canonical]); grind; done)

theorem spec_CheckedU128_is_overflowed : _root_.spec_CheckedU128_is_overflowed canonical := by
  unfold _root_.spec_CheckedU128_is_overflowed
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); grind; done)

theorem spec_CheckedU128_unwrap : _root_.spec_CheckedU128_unwrap canonical := by
  unfold _root_.spec_CheckedU128_unwrap
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); grind; done)

theorem spec_CheckedU128_to_option : _root_.spec_CheckedU128_to_option canonical := by
  unfold _root_.spec_CheckedU128_to_option
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); grind; done)

theorem spec_CheckedU16_is_overflowed : _root_.spec_CheckedU16_is_overflowed canonical := by
  unfold _root_.spec_CheckedU16_is_overflowed
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); grind; done)

theorem spec_CheckedU16_unwrap : _root_.spec_CheckedU16_unwrap canonical := by
  unfold _root_.spec_CheckedU16_unwrap
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); grind; done)

theorem spec_CheckedU16_to_option : _root_.spec_CheckedU16_to_option canonical := by
  unfold _root_.spec_CheckedU16_to_option
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); grind; done)

theorem spec_CheckedU32_is_overflowed : _root_.spec_CheckedU32_is_overflowed canonical := by
  unfold _root_.spec_CheckedU32_is_overflowed
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); grind; done)

theorem spec_CheckedU32_unwrap : _root_.spec_CheckedU32_unwrap canonical := by
  unfold _root_.spec_CheckedU32_unwrap
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); grind; done)

theorem spec_CheckedU32_to_option : _root_.spec_CheckedU32_to_option canonical := by
  unfold _root_.spec_CheckedU32_to_option
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); grind; done)

theorem spec_CheckedU64_is_overflowed : _root_.spec_CheckedU64_is_overflowed canonical := by
  unfold _root_.spec_CheckedU64_is_overflowed
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); grind; done)

theorem spec_CheckedU64_unwrap : _root_.spec_CheckedU64_unwrap canonical := by
  unfold _root_.spec_CheckedU64_unwrap
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); grind; done)

theorem spec_CheckedU64_to_option : _root_.spec_CheckedU64_to_option canonical := by
  unfold _root_.spec_CheckedU64_to_option
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); grind; done)

theorem spec_CheckedU8_is_overflowed : _root_.spec_CheckedU8_is_overflowed canonical := by
  unfold _root_.spec_CheckedU8_is_overflowed
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); grind; done)

theorem spec_CheckedU8_unwrap : _root_.spec_CheckedU8_unwrap canonical := by
  unfold _root_.spec_CheckedU8_unwrap
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap]); grind; done)

theorem spec_CheckedU8_to_option : _root_.spec_CheckedU8_to_option canonical := by
  unfold _root_.spec_CheckedU8_to_option
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option]); grind; done)

theorem spec_CheckedUsize_is_overflowed : _root_.spec_CheckedUsize_is_overflowed canonical := by
  unfold _root_.spec_CheckedUsize_is_overflowed
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_well_formed]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_well_formed]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_well_formed]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_well_formed]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_well_formed]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_well_formed]); grind; done)

theorem spec_CheckedUsize_unwrap : _root_.spec_CheckedUsize_unwrap canonical := by
  unfold _root_.spec_CheckedUsize_unwrap
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_well_formed]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_well_formed]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_well_formed]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_well_formed]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_well_formed]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_well_formed]); grind; done)

theorem spec_CheckedUsize_to_option : _root_.spec_CheckedUsize_to_option canonical := by
  unfold _root_.spec_CheckedUsize_to_option
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_well_formed]); done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_well_formed]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_well_formed]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_well_formed]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_well_formed]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_mul_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_mul_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_mul_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_mul_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_mul_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_mul_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_well_formed]); grind; done)

theorem spec_lemma_pow0 : _root_.spec_lemma_pow0 canonical := by
  unfold _root_.spec_lemma_pow0
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.pow]); done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); grind; done)

theorem spec_lemma_square_is_pow2 : _root_.spec_lemma_square_is_pow2 canonical := by
  unfold _root_.spec_lemma_square_is_pow2
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.pow]); done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); grind; done)

theorem spec_lemma_pow1 : _root_.spec_lemma_pow1 canonical := by
  unfold _root_.spec_lemma_pow1
  intros
  first
  | rfl
  | ((try simp_all [canonical, ArithmeticV2.pow]); done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); omega; done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); aesop; done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); ring; done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); nlinarith; done)
  | ((try simp_all [canonical, ArithmeticV2.pow]); grind; done)


theorem spec_CheckedU128_new : _root_.spec_CheckedU128_new canonical := by
  unfold _root_.spec_CheckedU128_new
  intros
  simp_all +zetaDelta only [canonical, checkedU128Max, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_spec_new, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_clone, ArithmeticV2.CheckedU128_new, ArithmeticV2.CheckedU128_new_overflowed, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU128Max, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_spec_new, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_clone, ArithmeticV2.CheckedU128_new, ArithmeticV2.CheckedU128_new_overflowed, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU128_new_overflowed : _root_.spec_CheckedU128_new_overflowed canonical := by
  unfold _root_.spec_CheckedU128_new_overflowed
  intros
  simp_all +zetaDelta only [canonical, checkedU128Max, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_spec_new, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_clone, ArithmeticV2.CheckedU128_new, ArithmeticV2.CheckedU128_new_overflowed, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU128Max, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_spec_new, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_clone, ArithmeticV2.CheckedU128_new, ArithmeticV2.CheckedU128_new_overflowed, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU128_add_value : _root_.spec_CheckedU128_add_value canonical := by
  unfold _root_.spec_CheckedU128_add_value
  intros
  simp_all +zetaDelta only [canonical, checkedU128Max, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_spec_new, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_clone, ArithmeticV2.CheckedU128_new, ArithmeticV2.CheckedU128_new_overflowed, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU128Max, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_spec_new, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_clone, ArithmeticV2.CheckedU128_new, ArithmeticV2.CheckedU128_new_overflowed, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU128_add_checked : _root_.spec_CheckedU128_add_checked canonical := by
  unfold _root_.spec_CheckedU128_add_checked
  intros
  simp_all +zetaDelta only [canonical, checkedU128Max, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_spec_new, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_clone, ArithmeticV2.CheckedU128_new, ArithmeticV2.CheckedU128_new_overflowed, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU128Max, ArithmeticV2.CheckedU128_view, ArithmeticV2.CheckedU128_spec_new, ArithmeticV2.CheckedU128_well_formed, ArithmeticV2.CheckedU128_spec_is_overflowed, ArithmeticV2.CheckedU128_clone, ArithmeticV2.CheckedU128_new, ArithmeticV2.CheckedU128_new_overflowed, ArithmeticV2.CheckedU128_is_overflowed, ArithmeticV2.CheckedU128_unwrap, ArithmeticV2.CheckedU128_to_option, ArithmeticV2.CheckedU128_add_value, ArithmeticV2.CheckedU128_add_checked, ArithmeticV2.CheckedU128_mul_value, ArithmeticV2.CheckedU128_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU16_new : _root_.spec_CheckedU16_new canonical := by
  unfold _root_.spec_CheckedU16_new
  intros
  simp_all +zetaDelta only [canonical, checkedU16Max, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_spec_new, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_clone, ArithmeticV2.CheckedU16_new, ArithmeticV2.CheckedU16_new_overflowed, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU16Max, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_spec_new, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_clone, ArithmeticV2.CheckedU16_new, ArithmeticV2.CheckedU16_new_overflowed, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU16_new_overflowed : _root_.spec_CheckedU16_new_overflowed canonical := by
  unfold _root_.spec_CheckedU16_new_overflowed
  intros
  simp_all +zetaDelta only [canonical, checkedU16Max, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_spec_new, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_clone, ArithmeticV2.CheckedU16_new, ArithmeticV2.CheckedU16_new_overflowed, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU16Max, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_spec_new, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_clone, ArithmeticV2.CheckedU16_new, ArithmeticV2.CheckedU16_new_overflowed, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU16_add_value : _root_.spec_CheckedU16_add_value canonical := by
  unfold _root_.spec_CheckedU16_add_value
  intros
  simp_all +zetaDelta only [canonical, checkedU16Max, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_spec_new, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_clone, ArithmeticV2.CheckedU16_new, ArithmeticV2.CheckedU16_new_overflowed, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU16Max, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_spec_new, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_clone, ArithmeticV2.CheckedU16_new, ArithmeticV2.CheckedU16_new_overflowed, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU16_add_checked : _root_.spec_CheckedU16_add_checked canonical := by
  unfold _root_.spec_CheckedU16_add_checked
  intros
  simp_all +zetaDelta only [canonical, checkedU16Max, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_spec_new, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_clone, ArithmeticV2.CheckedU16_new, ArithmeticV2.CheckedU16_new_overflowed, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU16Max, ArithmeticV2.CheckedU16_view, ArithmeticV2.CheckedU16_spec_new, ArithmeticV2.CheckedU16_well_formed, ArithmeticV2.CheckedU16_spec_is_overflowed, ArithmeticV2.CheckedU16_clone, ArithmeticV2.CheckedU16_new, ArithmeticV2.CheckedU16_new_overflowed, ArithmeticV2.CheckedU16_is_overflowed, ArithmeticV2.CheckedU16_unwrap, ArithmeticV2.CheckedU16_to_option, ArithmeticV2.CheckedU16_add_value, ArithmeticV2.CheckedU16_add_checked, ArithmeticV2.CheckedU16_mul_value, ArithmeticV2.CheckedU16_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU32_new : _root_.spec_CheckedU32_new canonical := by
  unfold _root_.spec_CheckedU32_new
  intros
  simp_all +zetaDelta only [canonical, checkedU32Max, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_spec_new, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_clone, ArithmeticV2.CheckedU32_new, ArithmeticV2.CheckedU32_new_overflowed, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU32Max, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_spec_new, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_clone, ArithmeticV2.CheckedU32_new, ArithmeticV2.CheckedU32_new_overflowed, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU32_new_overflowed : _root_.spec_CheckedU32_new_overflowed canonical := by
  unfold _root_.spec_CheckedU32_new_overflowed
  intros
  simp_all +zetaDelta only [canonical, checkedU32Max, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_spec_new, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_clone, ArithmeticV2.CheckedU32_new, ArithmeticV2.CheckedU32_new_overflowed, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU32Max, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_spec_new, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_clone, ArithmeticV2.CheckedU32_new, ArithmeticV2.CheckedU32_new_overflowed, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU32_add_value : _root_.spec_CheckedU32_add_value canonical := by
  unfold _root_.spec_CheckedU32_add_value
  intros
  simp_all +zetaDelta only [canonical, checkedU32Max, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_spec_new, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_clone, ArithmeticV2.CheckedU32_new, ArithmeticV2.CheckedU32_new_overflowed, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU32Max, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_spec_new, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_clone, ArithmeticV2.CheckedU32_new, ArithmeticV2.CheckedU32_new_overflowed, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU32_add_checked : _root_.spec_CheckedU32_add_checked canonical := by
  unfold _root_.spec_CheckedU32_add_checked
  intros
  simp_all +zetaDelta only [canonical, checkedU32Max, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_spec_new, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_clone, ArithmeticV2.CheckedU32_new, ArithmeticV2.CheckedU32_new_overflowed, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU32Max, ArithmeticV2.CheckedU32_view, ArithmeticV2.CheckedU32_spec_new, ArithmeticV2.CheckedU32_well_formed, ArithmeticV2.CheckedU32_spec_is_overflowed, ArithmeticV2.CheckedU32_clone, ArithmeticV2.CheckedU32_new, ArithmeticV2.CheckedU32_new_overflowed, ArithmeticV2.CheckedU32_is_overflowed, ArithmeticV2.CheckedU32_unwrap, ArithmeticV2.CheckedU32_to_option, ArithmeticV2.CheckedU32_add_value, ArithmeticV2.CheckedU32_add_checked, ArithmeticV2.CheckedU32_mul_value, ArithmeticV2.CheckedU32_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU64_new : _root_.spec_CheckedU64_new canonical := by
  unfold _root_.spec_CheckedU64_new
  intros
  simp_all +zetaDelta only [canonical, checkedU64Max, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_spec_new, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_clone, ArithmeticV2.CheckedU64_new, ArithmeticV2.CheckedU64_new_overflowed, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU64Max, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_spec_new, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_clone, ArithmeticV2.CheckedU64_new, ArithmeticV2.CheckedU64_new_overflowed, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU64_new_overflowed : _root_.spec_CheckedU64_new_overflowed canonical := by
  unfold _root_.spec_CheckedU64_new_overflowed
  intros
  simp_all +zetaDelta only [canonical, checkedU64Max, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_spec_new, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_clone, ArithmeticV2.CheckedU64_new, ArithmeticV2.CheckedU64_new_overflowed, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU64Max, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_spec_new, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_clone, ArithmeticV2.CheckedU64_new, ArithmeticV2.CheckedU64_new_overflowed, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU64_add_value : _root_.spec_CheckedU64_add_value canonical := by
  unfold _root_.spec_CheckedU64_add_value
  intros
  simp_all +zetaDelta only [canonical, checkedU64Max, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_spec_new, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_clone, ArithmeticV2.CheckedU64_new, ArithmeticV2.CheckedU64_new_overflowed, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU64Max, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_spec_new, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_clone, ArithmeticV2.CheckedU64_new, ArithmeticV2.CheckedU64_new_overflowed, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU64_add_checked : _root_.spec_CheckedU64_add_checked canonical := by
  unfold _root_.spec_CheckedU64_add_checked
  intros
  simp_all +zetaDelta only [canonical, checkedU64Max, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_spec_new, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_clone, ArithmeticV2.CheckedU64_new, ArithmeticV2.CheckedU64_new_overflowed, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU64Max, ArithmeticV2.CheckedU64_view, ArithmeticV2.CheckedU64_spec_new, ArithmeticV2.CheckedU64_well_formed, ArithmeticV2.CheckedU64_spec_is_overflowed, ArithmeticV2.CheckedU64_clone, ArithmeticV2.CheckedU64_new, ArithmeticV2.CheckedU64_new_overflowed, ArithmeticV2.CheckedU64_is_overflowed, ArithmeticV2.CheckedU64_unwrap, ArithmeticV2.CheckedU64_to_option, ArithmeticV2.CheckedU64_add_value, ArithmeticV2.CheckedU64_add_checked, ArithmeticV2.CheckedU64_mul_value, ArithmeticV2.CheckedU64_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU8_new : _root_.spec_CheckedU8_new canonical := by
  unfold _root_.spec_CheckedU8_new
  intros
  simp_all +zetaDelta only [canonical, checkedU8Max, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_spec_new, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_clone, ArithmeticV2.CheckedU8_new, ArithmeticV2.CheckedU8_new_overflowed, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU8Max, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_spec_new, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_clone, ArithmeticV2.CheckedU8_new, ArithmeticV2.CheckedU8_new_overflowed, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU8_new_overflowed : _root_.spec_CheckedU8_new_overflowed canonical := by
  unfold _root_.spec_CheckedU8_new_overflowed
  intros
  simp_all +zetaDelta only [canonical, checkedU8Max, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_spec_new, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_clone, ArithmeticV2.CheckedU8_new, ArithmeticV2.CheckedU8_new_overflowed, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU8Max, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_spec_new, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_clone, ArithmeticV2.CheckedU8_new, ArithmeticV2.CheckedU8_new_overflowed, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU8_add_value : _root_.spec_CheckedU8_add_value canonical := by
  unfold _root_.spec_CheckedU8_add_value
  intros
  simp_all +zetaDelta only [canonical, checkedU8Max, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_spec_new, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_clone, ArithmeticV2.CheckedU8_new, ArithmeticV2.CheckedU8_new_overflowed, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU8Max, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_spec_new, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_clone, ArithmeticV2.CheckedU8_new, ArithmeticV2.CheckedU8_new_overflowed, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedU8_add_checked : _root_.spec_CheckedU8_add_checked canonical := by
  unfold _root_.spec_CheckedU8_add_checked
  intros
  simp_all +zetaDelta only [canonical, checkedU8Max, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_spec_new, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_clone, ArithmeticV2.CheckedU8_new, ArithmeticV2.CheckedU8_new_overflowed, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedU8Max, ArithmeticV2.CheckedU8_view, ArithmeticV2.CheckedU8_spec_new, ArithmeticV2.CheckedU8_well_formed, ArithmeticV2.CheckedU8_spec_is_overflowed, ArithmeticV2.CheckedU8_clone, ArithmeticV2.CheckedU8_new, ArithmeticV2.CheckedU8_new_overflowed, ArithmeticV2.CheckedU8_is_overflowed, ArithmeticV2.CheckedU8_unwrap, ArithmeticV2.CheckedU8_to_option, ArithmeticV2.CheckedU8_add_value, ArithmeticV2.CheckedU8_add_checked, ArithmeticV2.CheckedU8_mul_value, ArithmeticV2.CheckedU8_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedUsize_new : _root_.spec_CheckedUsize_new canonical := by
  unfold _root_.spec_CheckedUsize_new
  intros
  simp_all +zetaDelta only [canonical, checkedUsizeMax, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_spec_new, ArithmeticV2.CheckedUsize_well_formed, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_clone, ArithmeticV2.CheckedUsize_new, ArithmeticV2.CheckedUsize_new_overflowed, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedUsizeMax, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_spec_new, ArithmeticV2.CheckedUsize_well_formed, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_clone, ArithmeticV2.CheckedUsize_new, ArithmeticV2.CheckedUsize_new_overflowed, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedUsize_new_overflowed : _root_.spec_CheckedUsize_new_overflowed canonical := by
  unfold _root_.spec_CheckedUsize_new_overflowed
  intros
  simp_all +zetaDelta only [canonical, checkedUsizeMax, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_spec_new, ArithmeticV2.CheckedUsize_well_formed, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_clone, ArithmeticV2.CheckedUsize_new, ArithmeticV2.CheckedUsize_new_overflowed, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedUsizeMax, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_spec_new, ArithmeticV2.CheckedUsize_well_formed, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_clone, ArithmeticV2.CheckedUsize_new, ArithmeticV2.CheckedUsize_new_overflowed, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedUsize_add_value : _root_.spec_CheckedUsize_add_value canonical := by
  unfold _root_.spec_CheckedUsize_add_value
  intros
  simp_all +zetaDelta only [canonical, checkedUsizeMax, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_spec_new, ArithmeticV2.CheckedUsize_well_formed, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_clone, ArithmeticV2.CheckedUsize_new, ArithmeticV2.CheckedUsize_new_overflowed, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedUsizeMax, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_spec_new, ArithmeticV2.CheckedUsize_well_formed, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_clone, ArithmeticV2.CheckedUsize_new, ArithmeticV2.CheckedUsize_new_overflowed, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_mul_checked] <;> first | omega | nlinarith

theorem spec_CheckedUsize_add_checked : _root_.spec_CheckedUsize_add_checked canonical := by
  unfold _root_.spec_CheckedUsize_add_checked
  intros
  simp_all +zetaDelta only [canonical, checkedUsizeMax, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_spec_new, ArithmeticV2.CheckedUsize_well_formed, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_clone, ArithmeticV2.CheckedUsize_new, ArithmeticV2.CheckedUsize_new_overflowed, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_mul_checked]
  all_goals repeat' (split at *)
  all_goals simp_all +zetaDelta [canonical, checkedUsizeMax, ArithmeticV2.CheckedUsize_view, ArithmeticV2.CheckedUsize_spec_new, ArithmeticV2.CheckedUsize_well_formed, ArithmeticV2.CheckedUsize_spec_is_overflowed, ArithmeticV2.CheckedUsize_clone, ArithmeticV2.CheckedUsize_new, ArithmeticV2.CheckedUsize_new_overflowed, ArithmeticV2.CheckedUsize_is_overflowed, ArithmeticV2.CheckedUsize_unwrap, ArithmeticV2.CheckedUsize_to_option, ArithmeticV2.CheckedUsize_add_value, ArithmeticV2.CheckedUsize_add_checked, ArithmeticV2.CheckedUsize_mul_value, ArithmeticV2.CheckedUsize_mul_checked] <;> first | omega | nlinarith

theorem spec_lemma_div_basics_4 : _root_.spec_lemma_div_basics_4 canonical := by
  intro x y h
  exact Int.ediv_nonneg h.1 (Int.le_of_lt h.2)

theorem spec_lemma_div_pos_is_pos : _root_.spec_lemma_div_pos_is_pos canonical := by
  intro x d h
  exact Int.ediv_nonneg h.1 (Int.le_of_lt h.2)

theorem spec_lemma_small_div_converse : _root_.spec_lemma_small_div_converse canonical := by
  intro x d h
  have hh := Int.emod_lt_of_pos x h.2.1
  have he := Int.ediv_mul_add_emod x d
  rw [h.2.2] at he
  omega

theorem spec_lemma_div_is_strictly_smaller : _root_.spec_lemma_div_is_strictly_smaller canonical := by
  intro x d h
  apply (Int.ediv_lt_iff_lt_mul (by omega : 0 < d)).mpr
  nlinarith

theorem spec_lemma_div_decreases : _root_.spec_lemma_div_decreases canonical := by
  intro x d h
  apply (Int.ediv_lt_iff_lt_mul (by omega : 0 < d)).mpr
  nlinarith

theorem spec_lemma_div_is_ordered : _root_.spec_lemma_div_is_ordered canonical := by
  intro x y z h
  exact Int.ediv_le_ediv h.2 h.1

theorem spec_lemma_div_nonincreasing : _root_.spec_lemma_div_nonincreasing canonical := by
  intro x d h
  exact Int.ediv_le_self d h.1

theorem spec_lemma_basic_div_specific_divisor : _root_.spec_lemma_basic_div_specific_divisor canonical := by
  intro d hd x hx
  exact Int.ediv_eq_zero_of_lt hx.1 hx.2

theorem spec_lemma_remainder_upper : _root_.spec_lemma_remainder_upper canonical := by
  intro x d h
  have hh := Int.emod_lt_of_pos x h.2
  have he := Int.ediv_mul_add_emod x d
  omega

theorem spec_lemma_remainder_lower : _root_.spec_lemma_remainder_lower canonical := by
  intro x d h
  have hh := Int.emod_nonneg x (by omega : d ≠ 0)
  have he := Int.ediv_mul_add_emod x d
  omega

theorem spec_lemma_remainder : _root_.spec_lemma_remainder canonical := by
  intro x d h
  have hl := Int.emod_nonneg x (by omega : d ≠ 0)
  have hh := Int.emod_lt_of_pos x h.2
  have he := Int.ediv_mul_add_emod x d
  omega

theorem spec_lemma_div_plus_one : _root_.spec_lemma_div_plus_one canonical := by
  intro x d hd
  rw [Int.add_ediv_of_dvd_left (dvd_refl d)]
  simp [Int.ediv_self (by omega : d ≠ 0)]

theorem spec_lemma_div_minus_one : _root_.spec_lemma_div_minus_one canonical := by
  intro x d hd
  rw [Int.add_ediv_of_dvd_left (by simp)]
  rw [Int.neg_ediv_of_dvd (dvd_refl d)]
  simp [Int.ediv_self (by omega : d ≠ 0), Int.neg_ediv_of_dvd (dvd_refl d)]


end ArithmeticCertificates
