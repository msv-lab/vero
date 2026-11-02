import JsonPatch.Spec.Patch
import JsonPatch.Spec.Pointer
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_resolve_nil : spec_resolve_nil canonical := by
  unfold spec_resolve_nil
  intros
  rfl

#print axioms structural_spec_resolve_nil

theorem structural_spec_apply_nil : spec_apply_nil canonical := by
  unfold spec_apply_nil
  intros
  rfl

#print axioms structural_spec_apply_nil

theorem structural_spec_apply_cons : spec_apply_cons canonical := by
  unfold spec_apply_cons
  intros
  rfl

#print axioms structural_spec_apply_cons
