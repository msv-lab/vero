import Greenery.Spec.Algebra
import Greenery.Spec.Fsm
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_accepts_nil : spec_accepts_nil canonical := by
  unfold spec_accepts_nil
  intros
  rfl

#print axioms structural_spec_accepts_nil
