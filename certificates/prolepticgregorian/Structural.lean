import ProlepticGregorian.Spec.Ordinal
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_days_in_month_feb : spec_days_in_month_feb canonical := by
  unfold spec_days_in_month_feb
  intros
  rfl

#print axioms structural_spec_days_in_month_feb

theorem structural_spec_ord_jan1 : spec_ord_jan1 canonical := by
  unfold spec_ord_jan1
  intros
  rfl

#print axioms structural_spec_ord_jan1

theorem structural_spec_ord_day_step : spec_ord_day_step canonical := by
  unfold spec_ord_day_step
  intros
  rfl

#print axioms structural_spec_ord_day_step
