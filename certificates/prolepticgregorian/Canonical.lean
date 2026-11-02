import Aesop
import Lean.Elab.Tactic.Omega
import ProlepticGregorian.Spec.Ordinal
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_days_in_month_table : spec_days_in_month_table canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_days_in_month_table, canonical, ProlepticGregorian.daysInMonth, ProlepticGregorian.isLeap, ProlepticGregorian.ord2ymd, ProlepticGregorian.validDate, ProlepticGregorian.weekday, ProlepticGregorian.ymd2ord]
  | solve | unfold spec_days_in_month_table; dsimp [canonical]; aesop
  | solve | unfold spec_days_in_month_table; dsimp [canonical]; intros; omega

#print axioms canonical_spec_days_in_month_table

theorem canonical_spec_leap_known : spec_leap_known canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_leap_known, canonical, ProlepticGregorian.daysInMonth, ProlepticGregorian.isLeap, ProlepticGregorian.ord2ymd, ProlepticGregorian.validDate, ProlepticGregorian.weekday, ProlepticGregorian.ymd2ord]
  | solve | unfold spec_leap_known; dsimp [canonical]; aesop
  | solve | unfold spec_leap_known; dsimp [canonical]; intros; omega

#print axioms canonical_spec_leap_known

theorem canonical_spec_ord_anchor : spec_ord_anchor canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_ord_anchor, canonical, ProlepticGregorian.daysInMonth, ProlepticGregorian.isLeap, ProlepticGregorian.ord2ymd, ProlepticGregorian.validDate, ProlepticGregorian.weekday, ProlepticGregorian.ymd2ord]
  | solve | unfold spec_ord_anchor; dsimp [canonical]; aesop
  | solve | unfold spec_ord_anchor; dsimp [canonical]; intros; omega

#print axioms canonical_spec_ord_anchor

theorem canonical_spec_weekday_anchor : spec_weekday_anchor canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_weekday_anchor, canonical, ProlepticGregorian.daysInMonth, ProlepticGregorian.isLeap, ProlepticGregorian.ord2ymd, ProlepticGregorian.validDate, ProlepticGregorian.weekday, ProlepticGregorian.ymd2ord]
  | solve | unfold spec_weekday_anchor; dsimp [canonical]; aesop
  | solve | unfold spec_weekday_anchor; dsimp [canonical]; intros; omega

#print axioms canonical_spec_weekday_anchor

theorem canonical_spec_weekday_known : spec_weekday_known canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_weekday_known, canonical, ProlepticGregorian.daysInMonth, ProlepticGregorian.isLeap, ProlepticGregorian.ord2ymd, ProlepticGregorian.validDate, ProlepticGregorian.weekday, ProlepticGregorian.ymd2ord]
  | solve | unfold spec_weekday_known; dsimp [canonical]; aesop
  | solve | unfold spec_weekday_known; dsimp [canonical]; intros; omega

#print axioms canonical_spec_weekday_known
