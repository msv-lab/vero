import Aesop
import Lean.Elab.Tactic.Omega
import Textwrap.Spec.Wrap
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_wrap_empty : spec_wrap_empty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_wrap_empty, canonical, Textwrap.shorten, Textwrap.wrap]
  | solve | unfold spec_wrap_empty; dsimp [canonical]; aesop
  | solve | unfold spec_wrap_empty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_wrap_empty

theorem canonical_spec_shorten_nil : spec_shorten_nil canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_shorten_nil, canonical, Textwrap.shorten, Textwrap.wrap]
  | solve | unfold spec_shorten_nil; dsimp [canonical]; aesop
  | solve | unfold spec_shorten_nil; dsimp [canonical]; intros; omega

#print axioms canonical_spec_shorten_nil
