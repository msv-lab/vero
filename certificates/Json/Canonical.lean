import Aesop
import Lean.Elab.Tactic.Omega
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
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_lex_string_start_quote : spec_lex_string_start_quote canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_lex_string_start_quote, canonical, JSON.apiSerializeAlloc, JSON.chain_CopyTo, JSON.concat, JSON.intToBytes, JSON.join, JSON.lexString, JSON.parametricConversion_ToNat_any, JSON.parametricEscaping_Escape, JSON.parametricEscaping_Unescape, JSON.stringBody, JSON.vector_Ensure, JSON.vector_PopFast, JSON.vector_Push, JSON.vector_PushFast, JSON.vector_Put, JSON.vector_Realloc, JSON.vector_ReallocDefault, JSON.view__CopyTo, JSON.writer__Append, JSON.writer__CopyTo, JSON.writer__ToArray, JSON.zcApiSerializeAlloc, serializer_array, serializer_bool, serializer_int, serializer_json, serializer_keyValue, serializer_number, serializer_object, serializer_string, serializer_value]
  | solve | unfold spec_lex_string_start_quote; dsimp [canonical]; aesop
  | solve | unfold spec_lex_string_start_quote; dsimp [canonical]; intros; omega

#print axioms canonical_spec_lex_string_start_quote

theorem canonical_spec_lex_string_body_unescaped_quote_ends : spec_lex_string_body_unescaped_quote_ends canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_lex_string_body_unescaped_quote_ends, canonical, JSON.apiSerializeAlloc, JSON.chain_CopyTo, JSON.concat, JSON.intToBytes, JSON.join, JSON.lexString, JSON.parametricConversion_ToNat_any, JSON.parametricEscaping_Escape, JSON.parametricEscaping_Unescape, JSON.stringBody, JSON.vector_Ensure, JSON.vector_PopFast, JSON.vector_Push, JSON.vector_PushFast, JSON.vector_Put, JSON.vector_Realloc, JSON.vector_ReallocDefault, JSON.view__CopyTo, JSON.writer__Append, JSON.writer__CopyTo, JSON.writer__ToArray, JSON.zcApiSerializeAlloc, serializer_array, serializer_bool, serializer_int, serializer_json, serializer_keyValue, serializer_number, serializer_object, serializer_string, serializer_value]
  | solve | unfold spec_lex_string_body_unescaped_quote_ends; dsimp [canonical]; aesop
  | solve | unfold spec_lex_string_body_unescaped_quote_ends; dsimp [canonical]; intros; omega

#print axioms canonical_spec_lex_string_body_unescaped_quote_ends

theorem canonical_spec_lex_string_body_escaped_quote_continues : spec_lex_string_body_escaped_quote_continues canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_lex_string_body_escaped_quote_continues, canonical, JSON.apiSerializeAlloc, JSON.chain_CopyTo, JSON.concat, JSON.intToBytes, JSON.join, JSON.lexString, JSON.parametricConversion_ToNat_any, JSON.parametricEscaping_Escape, JSON.parametricEscaping_Unescape, JSON.stringBody, JSON.vector_Ensure, JSON.vector_PopFast, JSON.vector_Push, JSON.vector_PushFast, JSON.vector_Put, JSON.vector_Realloc, JSON.vector_ReallocDefault, JSON.view__CopyTo, JSON.writer__Append, JSON.writer__CopyTo, JSON.writer__ToArray, JSON.zcApiSerializeAlloc, serializer_array, serializer_bool, serializer_int, serializer_json, serializer_keyValue, serializer_number, serializer_object, serializer_string, serializer_value]
  | solve | unfold spec_lex_string_body_escaped_quote_continues; dsimp [canonical]; aesop
  | solve | unfold spec_lex_string_body_escaped_quote_continues; dsimp [canonical]; intros; omega

#print axioms canonical_spec_lex_string_body_escaped_quote_continues

theorem canonical_spec_serializer_bool_true : spec_serializer_bool_true canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_serializer_bool_true, canonical, JSON.apiSerializeAlloc, JSON.chain_CopyTo, JSON.concat, JSON.intToBytes, JSON.join, JSON.lexString, JSON.parametricConversion_ToNat_any, JSON.parametricEscaping_Escape, JSON.parametricEscaping_Unescape, JSON.stringBody, JSON.vector_Ensure, JSON.vector_PopFast, JSON.vector_Push, JSON.vector_PushFast, JSON.vector_Put, JSON.vector_Realloc, JSON.vector_ReallocDefault, JSON.view__CopyTo, JSON.writer__Append, JSON.writer__CopyTo, JSON.writer__ToArray, JSON.zcApiSerializeAlloc, serializer_array, serializer_bool, serializer_int, serializer_json, serializer_keyValue, serializer_number, serializer_object, serializer_string, serializer_value]
  | solve | unfold spec_serializer_bool_true; dsimp [canonical]; aesop
  | solve | unfold spec_serializer_bool_true; dsimp [canonical]; intros; omega

#print axioms canonical_spec_serializer_bool_true

theorem canonical_spec_serializer_bool_false : spec_serializer_bool_false canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_serializer_bool_false, canonical, JSON.apiSerializeAlloc, JSON.chain_CopyTo, JSON.concat, JSON.intToBytes, JSON.join, JSON.lexString, JSON.parametricConversion_ToNat_any, JSON.parametricEscaping_Escape, JSON.parametricEscaping_Unescape, JSON.stringBody, JSON.vector_Ensure, JSON.vector_PopFast, JSON.vector_Push, JSON.vector_PushFast, JSON.vector_Put, JSON.vector_Realloc, JSON.vector_ReallocDefault, JSON.view__CopyTo, JSON.writer__Append, JSON.writer__CopyTo, JSON.writer__ToArray, JSON.zcApiSerializeAlloc, serializer_array, serializer_bool, serializer_int, serializer_json, serializer_keyValue, serializer_number, serializer_object, serializer_string, serializer_value]
  | solve | unfold spec_serializer_bool_false; dsimp [canonical]; aesop
  | solve | unfold spec_serializer_bool_false; dsimp [canonical]; intros; omega

#print axioms canonical_spec_serializer_bool_false

theorem canonical_spec_serializer_int_zero : spec_serializer_int_zero canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_serializer_int_zero, canonical, JSON.apiSerializeAlloc, JSON.chain_CopyTo, JSON.concat, JSON.intToBytes, JSON.join, JSON.lexString, JSON.parametricConversion_ToNat_any, JSON.parametricEscaping_Escape, JSON.parametricEscaping_Unescape, JSON.stringBody, JSON.vector_Ensure, JSON.vector_PopFast, JSON.vector_Push, JSON.vector_PushFast, JSON.vector_Put, JSON.vector_Realloc, JSON.vector_ReallocDefault, JSON.view__CopyTo, JSON.writer__Append, JSON.writer__CopyTo, JSON.writer__ToArray, JSON.zcApiSerializeAlloc, serializer_array, serializer_bool, serializer_int, serializer_json, serializer_keyValue, serializer_number, serializer_object, serializer_string, serializer_value]
  | solve | unfold spec_serializer_int_zero; dsimp [canonical]; aesop
  | solve | unfold spec_serializer_int_zero; dsimp [canonical]; intros; omega

#print axioms canonical_spec_serializer_int_zero

theorem canonical_spec_serializer_value_null : spec_serializer_value_null canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_serializer_value_null, canonical, JSON.apiSerializeAlloc, JSON.chain_CopyTo, JSON.concat, JSON.intToBytes, JSON.join, JSON.lexString, JSON.parametricConversion_ToNat_any, JSON.parametricEscaping_Escape, JSON.parametricEscaping_Unescape, JSON.stringBody, JSON.vector_Ensure, JSON.vector_PopFast, JSON.vector_Push, JSON.vector_PushFast, JSON.vector_Put, JSON.vector_Realloc, JSON.vector_ReallocDefault, JSON.view__CopyTo, JSON.writer__Append, JSON.writer__CopyTo, JSON.writer__ToArray, JSON.zcApiSerializeAlloc, serializer_array, serializer_bool, serializer_int, serializer_json, serializer_keyValue, serializer_number, serializer_object, serializer_string, serializer_value]
  | solve | unfold spec_serializer_value_null; dsimp [canonical]; aesop
  | solve | unfold spec_serializer_value_null; dsimp [canonical]; intros; omega

#print axioms canonical_spec_serializer_value_null

theorem canonical_spec_serializer_array_empty : spec_serializer_array_empty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_serializer_array_empty, canonical, JSON.apiSerializeAlloc, JSON.chain_CopyTo, JSON.concat, JSON.intToBytes, JSON.join, JSON.lexString, JSON.parametricConversion_ToNat_any, JSON.parametricEscaping_Escape, JSON.parametricEscaping_Unescape, JSON.stringBody, JSON.vector_Ensure, JSON.vector_PopFast, JSON.vector_Push, JSON.vector_PushFast, JSON.vector_Put, JSON.vector_Realloc, JSON.vector_ReallocDefault, JSON.view__CopyTo, JSON.writer__Append, JSON.writer__CopyTo, JSON.writer__ToArray, JSON.zcApiSerializeAlloc, serializer_array, serializer_bool, serializer_int, serializer_json, serializer_keyValue, serializer_number, serializer_object, serializer_string, serializer_value]
  | solve | unfold spec_serializer_array_empty; dsimp [canonical]; aesop
  | solve | unfold spec_serializer_array_empty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_serializer_array_empty

theorem canonical_spec_serializer_object_empty : spec_serializer_object_empty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_serializer_object_empty, canonical, JSON.apiSerializeAlloc, JSON.chain_CopyTo, JSON.concat, JSON.intToBytes, JSON.join, JSON.lexString, JSON.parametricConversion_ToNat_any, JSON.parametricEscaping_Escape, JSON.parametricEscaping_Unescape, JSON.stringBody, JSON.vector_Ensure, JSON.vector_PopFast, JSON.vector_Push, JSON.vector_PushFast, JSON.vector_Put, JSON.vector_Realloc, JSON.vector_ReallocDefault, JSON.view__CopyTo, JSON.writer__Append, JSON.writer__CopyTo, JSON.writer__ToArray, JSON.zcApiSerializeAlloc, serializer_array, serializer_bool, serializer_int, serializer_json, serializer_keyValue, serializer_number, serializer_object, serializer_string, serializer_value]
  | solve | unfold spec_serializer_object_empty; dsimp [canonical]; aesop
  | solve | unfold spec_serializer_object_empty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_serializer_object_empty
