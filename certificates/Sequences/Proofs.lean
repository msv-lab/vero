import SequencesV2.Spec.LittleEndianNat
import SequencesV2.Spec.LittleEndianNatConversions
import SequencesV2.Spec.MergeSort
import SequencesV2.Spec.Seq
import SequencesV2.Spec.Trusted
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Dedup
import Aesop
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000
set_option maxHeartbeats 30000
open SequencesV2
namespace SequencesCertificates

theorem spec_LittleEndianNat_LemmaToNatLeftEqToNatRight : _root_.spec_LittleEndianNat_LemmaToNatLeftEqToNatRight canonical := by
  unfold _root_.spec_LittleEndianNat_LemmaToNatLeftEqToNatRight
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.LittleEndianNat_BASE, SequencesV2.LittleEndianNat_FromNat, SequencesV2.LittleEndianNat_FromNatWithLen, SequencesV2.LittleEndianNat_SeqAdd, SequencesV2.LittleEndianNat_SeqExtend, SequencesV2.LittleEndianNat_SeqExtendMultiple, SequencesV2.LittleEndianNat_SeqSub, SequencesV2.LittleEndianNat_SeqZero, SequencesV2.LittleEndianNat_ToNatLeft, SequencesV2.LittleEndianNat_ToNatRight, SequencesV2.LittleEndianNat_isUint, SequencesV2.LittleEndianNat_validSeq]; done)
  | (simp_all [canonical, SequencesV2.LittleEndianNat_BASE, SequencesV2.LittleEndianNat_FromNat, SequencesV2.LittleEndianNat_FromNatWithLen, SequencesV2.LittleEndianNat_SeqAdd, SequencesV2.LittleEndianNat_SeqExtend, SequencesV2.LittleEndianNat_SeqExtendMultiple, SequencesV2.LittleEndianNat_SeqSub, SequencesV2.LittleEndianNat_SeqZero, SequencesV2.LittleEndianNat_ToNatLeft, SequencesV2.LittleEndianNat_ToNatRight, SequencesV2.LittleEndianNat_isUint, SequencesV2.LittleEndianNat_validSeq]; omega; done)
  | (simp_all [canonical, SequencesV2.LittleEndianNat_BASE, SequencesV2.LittleEndianNat_FromNat, SequencesV2.LittleEndianNat_FromNatWithLen, SequencesV2.LittleEndianNat_SeqAdd, SequencesV2.LittleEndianNat_SeqExtend, SequencesV2.LittleEndianNat_SeqExtendMultiple, SequencesV2.LittleEndianNat_SeqSub, SequencesV2.LittleEndianNat_SeqZero, SequencesV2.LittleEndianNat_ToNatLeft, SequencesV2.LittleEndianNat_ToNatRight, SequencesV2.LittleEndianNat_isUint, SequencesV2.LittleEndianNat_validSeq]; aesop; done)
  | (simp_all [canonical, SequencesV2.LittleEndianNat_BASE, SequencesV2.LittleEndianNat_FromNat, SequencesV2.LittleEndianNat_FromNatWithLen, SequencesV2.LittleEndianNat_SeqAdd, SequencesV2.LittleEndianNat_SeqExtend, SequencesV2.LittleEndianNat_SeqExtendMultiple, SequencesV2.LittleEndianNat_SeqSub, SequencesV2.LittleEndianNat_SeqZero, SequencesV2.LittleEndianNat_ToNatLeft, SequencesV2.LittleEndianNat_ToNatRight, SequencesV2.LittleEndianNat_isUint, SequencesV2.LittleEndianNat_validSeq]; ring; done)
  | (simp_all [canonical, SequencesV2.LittleEndianNat_BASE, SequencesV2.LittleEndianNat_FromNat, SequencesV2.LittleEndianNat_FromNatWithLen, SequencesV2.LittleEndianNat_SeqAdd, SequencesV2.LittleEndianNat_SeqExtend, SequencesV2.LittleEndianNat_SeqExtendMultiple, SequencesV2.LittleEndianNat_SeqSub, SequencesV2.LittleEndianNat_SeqZero, SequencesV2.LittleEndianNat_ToNatLeft, SequencesV2.LittleEndianNat_ToNatRight, SequencesV2.LittleEndianNat_isUint, SequencesV2.LittleEndianNat_validSeq]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.LittleEndianNat_BASE, SequencesV2.LittleEndianNat_FromNat, SequencesV2.LittleEndianNat_FromNatWithLen, SequencesV2.LittleEndianNat_SeqAdd, SequencesV2.LittleEndianNat_SeqExtend, SequencesV2.LittleEndianNat_SeqExtendMultiple, SequencesV2.LittleEndianNat_SeqSub, SequencesV2.LittleEndianNat_SeqZero, SequencesV2.LittleEndianNat_ToNatLeft, SequencesV2.LittleEndianNat_ToNatRight, SequencesV2.LittleEndianNat_isUint, SequencesV2.LittleEndianNat_validSeq]; grind; done)

theorem spec_LittleEndianNat_LemmaSeqAppendZero : _root_.spec_LittleEndianNat_LemmaSeqAppendZero canonical := by
  unfold _root_.spec_LittleEndianNat_LemmaSeqAppendZero
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.LittleEndianNat_BASE, SequencesV2.LittleEndianNat_FromNat, SequencesV2.LittleEndianNat_FromNatWithLen, SequencesV2.LittleEndianNat_SeqAdd, SequencesV2.LittleEndianNat_SeqExtend, SequencesV2.LittleEndianNat_SeqExtendMultiple, SequencesV2.LittleEndianNat_SeqSub, SequencesV2.LittleEndianNat_SeqZero, SequencesV2.LittleEndianNat_ToNatLeft, SequencesV2.LittleEndianNat_ToNatRight, SequencesV2.LittleEndianNat_isUint, SequencesV2.LittleEndianNat_validSeq]; done)
  | (simp_all [canonical, SequencesV2.LittleEndianNat_BASE, SequencesV2.LittleEndianNat_FromNat, SequencesV2.LittleEndianNat_FromNatWithLen, SequencesV2.LittleEndianNat_SeqAdd, SequencesV2.LittleEndianNat_SeqExtend, SequencesV2.LittleEndianNat_SeqExtendMultiple, SequencesV2.LittleEndianNat_SeqSub, SequencesV2.LittleEndianNat_SeqZero, SequencesV2.LittleEndianNat_ToNatLeft, SequencesV2.LittleEndianNat_ToNatRight, SequencesV2.LittleEndianNat_isUint, SequencesV2.LittleEndianNat_validSeq]; omega; done)
  | (simp_all [canonical, SequencesV2.LittleEndianNat_BASE, SequencesV2.LittleEndianNat_FromNat, SequencesV2.LittleEndianNat_FromNatWithLen, SequencesV2.LittleEndianNat_SeqAdd, SequencesV2.LittleEndianNat_SeqExtend, SequencesV2.LittleEndianNat_SeqExtendMultiple, SequencesV2.LittleEndianNat_SeqSub, SequencesV2.LittleEndianNat_SeqZero, SequencesV2.LittleEndianNat_ToNatLeft, SequencesV2.LittleEndianNat_ToNatRight, SequencesV2.LittleEndianNat_isUint, SequencesV2.LittleEndianNat_validSeq]; aesop; done)
  | (simp_all [canonical, SequencesV2.LittleEndianNat_BASE, SequencesV2.LittleEndianNat_FromNat, SequencesV2.LittleEndianNat_FromNatWithLen, SequencesV2.LittleEndianNat_SeqAdd, SequencesV2.LittleEndianNat_SeqExtend, SequencesV2.LittleEndianNat_SeqExtendMultiple, SequencesV2.LittleEndianNat_SeqSub, SequencesV2.LittleEndianNat_SeqZero, SequencesV2.LittleEndianNat_ToNatLeft, SequencesV2.LittleEndianNat_ToNatRight, SequencesV2.LittleEndianNat_isUint, SequencesV2.LittleEndianNat_validSeq]; ring; done)
  | (simp_all [canonical, SequencesV2.LittleEndianNat_BASE, SequencesV2.LittleEndianNat_FromNat, SequencesV2.LittleEndianNat_FromNatWithLen, SequencesV2.LittleEndianNat_SeqAdd, SequencesV2.LittleEndianNat_SeqExtend, SequencesV2.LittleEndianNat_SeqExtendMultiple, SequencesV2.LittleEndianNat_SeqSub, SequencesV2.LittleEndianNat_SeqZero, SequencesV2.LittleEndianNat_ToNatLeft, SequencesV2.LittleEndianNat_ToNatRight, SequencesV2.LittleEndianNat_isUint, SequencesV2.LittleEndianNat_validSeq]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.LittleEndianNat_BASE, SequencesV2.LittleEndianNat_FromNat, SequencesV2.LittleEndianNat_FromNatWithLen, SequencesV2.LittleEndianNat_SeqAdd, SequencesV2.LittleEndianNat_SeqExtend, SequencesV2.LittleEndianNat_SeqExtendMultiple, SequencesV2.LittleEndianNat_SeqSub, SequencesV2.LittleEndianNat_SeqZero, SequencesV2.LittleEndianNat_ToNatLeft, SequencesV2.LittleEndianNat_ToNatRight, SequencesV2.LittleEndianNat_isUint, SequencesV2.LittleEndianNat_validSeq]; grind; done)

theorem spec_Seq_First___ensures_spec : _root_.spec_Seq_First___ensures_spec canonical := by
  unfold _root_.spec_Seq_First___ensures_spec
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_DropFirst, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_First, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; done)
  | (simp_all [canonical, SequencesV2.Seq_DropFirst, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_First, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_DropFirst, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_First, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_DropFirst, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_First, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_DropFirst, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_First, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_DropFirst, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_First, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; grind; done)

theorem spec_Seq_LemmaLast : _root_.spec_Seq_LemmaLast canonical := by
  unfold _root_.spec_Seq_LemmaLast
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; grind; done)

theorem spec_Seq_Last___ensures_spec : _root_.spec_Seq_Last___ensures_spec canonical := by
  unfold _root_.spec_Seq_Last___ensures_spec
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; grind; done)

theorem spec_Seq_LemmaAppendLast : _root_.spec_Seq_LemmaAppendLast canonical := by
  unfold _root_.spec_Seq_LemmaAppendLast
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_DropLast, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_IndexOf, SequencesV2.Seq_IndexOfOption, SequencesV2.Seq_Insert, SequencesV2.Seq_Last, SequencesV2.Seq_LastIndexOf, SequencesV2.Seq_LastIndexOfOption, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult, SequencesV2.Seq_Max, SequencesV2.Seq_Min, SequencesV2.Seq_Remove, SequencesV2.Seq_RemoveValue, SequencesV2.Seq_Repeat, SequencesV2.Seq_Reverse, SequencesV2.Seq_ToArray, SequencesV2.Seq_Unzip, SequencesV2.Seq_Zip]; grind; done)

theorem spec_Seq_LemmaConcatIsAssociative : _root_.spec_Seq_LemmaConcatIsAssociative canonical := by
  unfold _root_.spec_Seq_LemmaConcatIsAssociative
  intros
  first
  | rfl
  | (simp_all [canonical]; done)
  | (simp_all [canonical]; omega; done)
  | (simp_all [canonical]; aesop; done)
  | (simp_all [canonical]; ring; done)
  | (simp_all [canonical]; nlinarith; done)
  | (simp_all [canonical]; grind; done)

theorem spec_Seq_LemmaNoDuplicatesInConcat : _root_.spec_Seq_LemmaNoDuplicatesInConcat canonical := by
  unfold _root_.spec_Seq_LemmaNoDuplicatesInConcat
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_Disjoint, SequencesV2.Seq_HasNoDuplicates]; done)
  | (simp_all [canonical, SequencesV2.Seq_Disjoint, SequencesV2.Seq_HasNoDuplicates]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_Disjoint, SequencesV2.Seq_HasNoDuplicates]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_Disjoint, SequencesV2.Seq_HasNoDuplicates]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_Disjoint, SequencesV2.Seq_HasNoDuplicates]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_Disjoint, SequencesV2.Seq_HasNoDuplicates]; grind; done)

theorem spec_Seq_Flatten___ensures_spec : _root_.spec_Seq_Flatten___ensures_spec canonical := by
  unfold _root_.spec_Seq_Flatten___ensures_spec
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; grind; done)

theorem spec_Seq_FlattenReverse___ensures_spec : _root_.spec_Seq_FlattenReverse___ensures_spec canonical := by
  unfold _root_.spec_Seq_FlattenReverse___ensures_spec
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; grind; done)

theorem spec_Seq_LemmaFlattenConcat : _root_.spec_Seq_LemmaFlattenConcat canonical := by
  unfold _root_.spec_Seq_LemmaFlattenConcat
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; grind; done)

theorem spec_Seq_LemmaFlattenReverseConcat : _root_.spec_Seq_LemmaFlattenReverseConcat canonical := by
  unfold _root_.spec_Seq_LemmaFlattenReverseConcat
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; grind; done)

theorem spec_Seq_LemmaFlattenAndFlattenReverseAreEquivalent : _root_.spec_Seq_LemmaFlattenAndFlattenReverseAreEquivalent canonical := by
  unfold _root_.spec_Seq_LemmaFlattenAndFlattenReverseAreEquivalent
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; grind; done)

theorem spec_Seq_FlatMap___ensures_spec : _root_.spec_Seq_FlatMap___ensures_spec canonical := by
  unfold _root_.spec_Seq_FlatMap___ensures_spec
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_Flatten, SequencesV2.Seq_FlattenReverse, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; grind; done)

theorem spec_Seq_LemmaMapDistributesOverConcat : _root_.spec_Seq_LemmaMapDistributesOverConcat canonical := by
  unfold _root_.spec_Seq_LemmaMapDistributesOverConcat
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight, SequencesV2.Seq_Map, SequencesV2.Seq_MapWithResult]; grind; done)

theorem spec_Seq_Filter___ensures_spec : _root_.spec_Seq_Filter___ensures_spec canonical := by
  unfold _root_.spec_Seq_Filter___ensures_spec
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; grind; done)

theorem spec_Seq_LemmaFilterDistributesOverConcat : _root_.spec_Seq_LemmaFilterDistributesOverConcat canonical := by
  unfold _root_.spec_Seq_LemmaFilterDistributesOverConcat
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_Filter, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; grind; done)

theorem spec_Seq_FoldLeft___ensures_spec : _root_.spec_Seq_FoldLeft___ensures_spec canonical := by
  unfold _root_.spec_Seq_FoldLeft___ensures_spec
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; grind; done)

theorem spec_Seq_LemmaFoldLeftDistributesOverConcat : _root_.spec_Seq_LemmaFoldLeftDistributesOverConcat canonical := by
  unfold _root_.spec_Seq_LemmaFoldLeftDistributesOverConcat
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldLeft, SequencesV2.Seq_FoldRight]; grind; done)

theorem spec_Seq_FoldRight___ensures_spec : _root_.spec_Seq_FoldRight___ensures_spec canonical := by
  unfold _root_.spec_Seq_FoldRight___ensures_spec
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldRight]; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldRight]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldRight]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldRight]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldRight]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldRight]; grind; done)

theorem spec_Seq_LemmaFoldRightDistributesOverConcat : _root_.spec_Seq_LemmaFoldRightDistributesOverConcat canonical := by
  unfold _root_.spec_Seq_LemmaFoldRightDistributesOverConcat
  intros
  first
  | rfl
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldRight]; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldRight]; omega; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldRight]; aesop; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldRight]; ring; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldRight]; nlinarith; done)
  | (simp_all [canonical, SequencesV2.Seq_FlatMap, SequencesV2.Seq_FoldRight]; grind; done)

end SequencesCertificates
