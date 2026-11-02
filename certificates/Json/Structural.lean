import JsonV2.Spec.API
import JsonV2.Spec.ConcreteSyntax.Spec
import JsonV2.Spec.ConcreteSyntax.SpecProperties
import JsonV2.Spec.Serializer
import JsonV2.Spec.Spec
import JsonV2.Spec.Utils.Cursors
import JsonV2.Spec.Utils.Lexers
import JsonV2.Spec.Utils.Seq
import JsonV2.Spec.Utils.Str
import JsonV2.Spec.Utils.Vectors
import JsonV2.Spec.Utils.Views
import JsonV2.Spec.Utils.Views.Writers
import JsonV2.Spec.ZeroCopy.API
set_option maxHeartbeats 1000
set_option maxRecDepth 512
theorem structural_spec_writer_append_bytes : spec_writer_append_bytes canonical := by
  unfold spec_writer_append_bytes
  intros
  rfl

#print axioms structural_spec_writer_append_bytes

theorem structural_spec_writer_to_array_correct : spec_writer_to_array_correct canonical := by
  unfold spec_writer_to_array_correct
  intros
  rfl

#print axioms structural_spec_writer_to_array_correct

theorem structural_spec_string_body_backslash_toggles_escape : spec_string_body_backslash_toggles_escape canonical := by
  unfold spec_string_body_backslash_toggles_escape
  intros
  rfl

#print axioms structural_spec_string_body_backslash_toggles_escape

theorem structural_spec_string_body_accept_unescaped_quote : spec_string_body_accept_unescaped_quote canonical := by
  unfold spec_string_body_accept_unescaped_quote
  intros
  rfl

#print axioms structural_spec_string_body_accept_unescaped_quote

theorem structural_spec_string_body_escaped_quote_continues : spec_string_body_escaped_quote_continues canonical := by
  unfold spec_string_body_escaped_quote_continues
  intros
  rfl

#print axioms structural_spec_string_body_escaped_quote_continues

theorem structural_spec_lex_string_end_accepts : spec_lex_string_end_accepts canonical := by
  unfold spec_lex_string_end_accepts
  intros
  rfl

#print axioms structural_spec_lex_string_end_accepts

theorem structural_spec_lex_string_body_backslash_toggles : spec_lex_string_body_backslash_toggles canonical := by
  unfold spec_lex_string_body_backslash_toggles
  intros
  rfl

#print axioms structural_spec_lex_string_body_backslash_toggles

theorem structural_spec_vector_put_updates_items : spec_vector_put_updates_items canonical := by
  unfold spec_vector_put_updates_items
  intros
  rfl

#print axioms structural_spec_vector_put_updates_items

theorem structural_spec_vector_put_preserves_capacity : spec_vector_put_preserves_capacity canonical := by
  unfold spec_vector_put_preserves_capacity
  intros
  rfl

#print axioms structural_spec_vector_put_preserves_capacity

theorem structural_spec_vector_pop_fast_removes_last : spec_vector_pop_fast_removes_last canonical := by
  unfold spec_vector_pop_fast_removes_last
  intros
  rfl

#print axioms structural_spec_vector_pop_fast_removes_last

theorem structural_spec_vector_pop_fast_preserves_capacity : spec_vector_pop_fast_preserves_capacity canonical := by
  unfold spec_vector_pop_fast_preserves_capacity
  intros
  rfl

#print axioms structural_spec_vector_pop_fast_preserves_capacity

theorem structural_spec_vector_push_fast_appends : spec_vector_push_fast_appends canonical := by
  unfold spec_vector_push_fast_appends
  intros
  rfl

#print axioms structural_spec_vector_push_fast_appends

theorem structural_spec_vector_push_fast_preserves_capacity : spec_vector_push_fast_preserves_capacity canonical := by
  unfold spec_vector_push_fast_preserves_capacity
  intros
  rfl

#print axioms structural_spec_vector_push_fast_preserves_capacity

theorem structural_spec_serializer_value_bool : spec_serializer_value_bool canonical := by
  unfold spec_serializer_value_bool
  intros
  rfl

#print axioms structural_spec_serializer_value_bool

theorem structural_spec_serializer_value_string : spec_serializer_value_string canonical := by
  unfold spec_serializer_value_string
  intros
  rfl

#print axioms structural_spec_serializer_value_string

theorem structural_spec_serializer_value_number : spec_serializer_value_number canonical := by
  unfold spec_serializer_value_number
  intros
  rfl

#print axioms structural_spec_serializer_value_number

theorem structural_spec_serializer_json_eq_value : spec_serializer_json_eq_value canonical := by
  unfold spec_serializer_json_eq_value
  intros
  rfl

#print axioms structural_spec_serializer_json_eq_value

theorem structural_spec_unfoldValueNumber : spec_unfoldValueNumber canonical := by
  unfold spec_unfoldValueNumber
  intros
  rfl

#print axioms structural_spec_unfoldValueNumber

theorem structural_spec_unfoldValueObject : spec_unfoldValueObject canonical := by
  unfold spec_unfoldValueObject
  intros
  rfl

#print axioms structural_spec_unfoldValueObject

theorem structural_spec_unfoldValueArray : spec_unfoldValueArray canonical := by
  unfold spec_unfoldValueArray
  intros
  rfl

#print axioms structural_spec_unfoldValueArray
