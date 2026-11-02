import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Base58.Spec.Codec
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
open Base58Spec
namespace Base58Certificates

theorem decode_int_positional_value : spec_decode_int_positional_value canonical := by
  intro s
  rfl

theorem decode_int_empty : spec_decode_int_empty canonical := by
  unfold spec_decode_int_empty
  decide

theorem encode_int_zero : spec_encode_int_zero canonical := by
  unfold spec_encode_int_zero
  decide

theorem encode_empty : spec_encode_empty canonical := by
  unfold spec_encode_empty
  decide

theorem vector_encode_int : spec_vector_encode_int canonical := by
  unfold spec_vector_encode_int
  decide

theorem vector_decode_int : spec_vector_decode_int canonical := by
  unfold spec_vector_decode_int
  decide

theorem vector_encode_bytes : spec_vector_encode_bytes canonical := by
  unfold spec_vector_encode_bytes
  decide

abbrev step (acc : Option Nat) (c : Char) : Option Nat :=
  match acc, b58Idx c with
  | some n, some d => some (n * 58 + d)
  | _, _ => none

theorem fold_none (cs : List Char) : cs.foldl step none = none := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simpa [step] using ih

theorem fold_invalid (cs : List Char) (acc : Option Nat)
    (h : cs.all (fun c => (b58Idx c).isSome) = false) : cs.foldl step acc = none := by
  induction cs generalizing acc with
  | nil => simp at h
  | cons c cs ih =>
    cases hc : b58Idx c with
    | none => simp [List.foldl_cons, step, hc, fold_none]
    | some d =>
      have ht : cs.all (fun c => (b58Idx c).isSome) = false := by simpa [hc] using h
      exact ih _ ht

theorem decode_int_invalid_char : spec_decode_int_invalid_char canonical := by
  intro s h
  exact fold_invalid s.toList (some 0) h

theorem decode_int_horner_step : spec_decode_int_horner_step canonical := by
  intro s c n d hs hc
  change (s ++ String.singleton c).toList.foldl step (some 0) = _
  simp only [String.toList_append, String.toList_singleton, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  change step (Base58.decodeInt s) c = _
  rw [show Base58.decodeInt s = some n from hs]
  simp [step, hc]

theorem leadingZeros_eq (bs : Bytes) : leadingZeroBytes bs = leadingZeroBytesGT bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [leadingZeroBytes, leadingZeroBytesGT, ih]

theorem dropZeros_eq (bs : Bytes) : dropLeadingZeroBytes bs = dropLeadingZeroBytesGT bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [dropLeadingZeroBytes, dropLeadingZeroBytesGT, ih]

theorem zeros_prefix (z : Nat) (bs : Bytes) :
    leadingZeroBytes (List.replicate z 0 ++ bs) = z + leadingZeroBytes bs ∧
    dropLeadingZeroBytes (List.replicate z 0 ++ bs) = dropLeadingZeroBytes bs := by
  induction z with
  | zero => simp
  | succ z ih => simp [List.replicate_succ, leadingZeroBytes, dropLeadingZeroBytes, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem encode_leading_zero_boundary : spec_encode_leading_zero_boundary canonical := by
  intro z b rest hb
  change Base58.encode _ = _
  simp [canonical, Base58.encode, (zeros_prefix z (b :: rest)).1,
    (zeros_prefix z (b :: rest)).2, leadingZeroBytes, dropLeadingZeroBytes, hb, beValue, beValueGT]

theorem encode_all_zeros : spec_encode_all_zeros canonical := by
  intro z
  have hp := zeros_prefix z []
  simp only [List.append_nil, leadingZeroBytes, dropLeadingZeroBytes, Nat.add_zero] at hp
  change Base58.encode _ = _
  simp [Base58.encode, hp.1, hp.2]

theorem encode_leading_zero_prefix_homomorphism : spec_encode_leading_zero_prefix_homomorphism canonical := by
  intro z bs
  change Base58.encode _ = _
  simp [canonical, Base58.encode, (zeros_prefix z bs).1, (zeros_prefix z bs).2,
    List.replicate_add, String.ofList_append, String.append_assoc, -List.replicate_append_replicate]

theorem toBytes_eq (n : Nat) : toBytes n = toBytesGT n := by
  have h : ∀ f n a, toBytesAux f n a = toBytesGTAux f n a := by
    intro f
    induction f with
    | zero => intros; rfl
    | succ f ih =>
      intro n a
      cases n with
      | zero => rfl
      | succ n => simpa [toBytesAux, toBytesGTAux] using ih ((n+1)/256) (((n+1)%256)::a)
  simp [toBytes, toBytesGT, h]

theorem leadingOnes_takeWhile (cs : List Char) :
    leadingOnes cs = (cs.takeWhile (· == '1')).length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => by_cases h : c = '1' <;> simp [leadingOnes, List.takeWhile_cons, h, ih]

theorem decode_value_bytes_decomposition : spec_decode_value_bytes_decomposition canonical := by
  intro s v hv
  change Base58.decode s = _
  simp [Base58.decode, show Base58.decodeInt (String.ofList (s.toList.dropWhile (· == '1'))) = some v from hv,
    ← leadingOnes_takeWhile, toBytes_eq]

theorem decode_invalid_char : spec_decode_invalid_char canonical := by
  intro s h
  change Base58.decode s = none
  simp [Base58.decode, show Base58.decodeInt (String.ofList (s.toList.dropWhile (· == '1'))) = none from
    decode_int_invalid_char _ h]

theorem decode_all_ones : spec_decode_all_ones canonical := by
  intro z
  change Base58.decode _ = _
  simp [Base58.decode, List.takeWhile_replicate, List.dropWhile_replicate, Base58.decodeInt, toBytes]

theorem idx_lt {c : Char} {d : Nat} (h : b58Idx c = some d) : d < 58 := by
  have hl := (List.idxOf?_eq_some_iff.mp h).1
  exact hl

theorem fold_offset (cs : List Char) (a b v : Nat)
    (h : cs.foldl step (some b) = some v) :
    cs.foldl step (some (a+b)) = some (a * 58 ^ cs.length + v) := by
  induction cs generalizing a b v with
  | nil => simp_all
  | cons c cs ih =>
    cases hc : b58Idx c with
    | none => simp [List.foldl_cons, step, hc, fold_none] at h
    | some d =>
      simp only [List.foldl_cons, step, hc] at h ⊢
      have hh := ih (a*58) (b*58+d) v h
      convert hh using 1 <;> congr 1 <;> simp [List.length_cons, Nat.pow_succ] <;> ring

theorem decode_int_concat_homomorphism : spec_decode_int_concat_homomorphism canonical := by
  intro s t p q hs ht
  change (s ++ t).toList.foldl step (some 0) = _
  simp only [String.toList_append, List.foldl_append]
  rw [show s.toList.foldl step (some 0) = some p from hs]
  simpa using fold_offset t.toList p 0 q ht

theorem fold_bound (cs : List Char) (a n : Nat)
    (h : cs.foldl step (some a) = some n) : n < (a+1)*58^cs.length := by
  induction cs generalizing a n with
  | nil => simp_all
  | cons c cs ih =>
    cases hc : b58Idx c with
    | none => simp [List.foldl_cons, step, hc, fold_none] at h
    | some d =>
      have hd := idx_lt hc
      have hh := ih (a*58+d) n (by simpa [List.foldl_cons, step, hc] using h)
      simp only [List.length_cons, Nat.pow_succ]
      have hp : 0 < 58 ^ cs.length := by positivity
      nlinarith

theorem decode_int_value_lt : spec_decode_int_value_lt canonical := by
  intro s n h
  have hh := fold_bound s.toList 0 n h
  simpa using hh

theorem decode_int_concat_div_mod : spec_decode_int_concat_div_mod canonical := by
  intro s t p q n hs ht hn
  have he := decode_int_concat_homomorphism s t p q hs ht
  have hn' : n = p * 58 ^ t.toList.length + q := Option.some.inj (hn.symm.trans he)
  have hq : q < 58^t.toList.length := by simpa using decode_int_value_lt t q ht
  rw [hn']
  constructor
  · change (p * 58 ^ t.toList.length + q) / 58 ^ t.toList.length = p
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hq, Nat.zero_add]
  · exact Nat.mul_add_mod_of_lt hq

theorem decode_int_split_digit_contribution : spec_decode_int_split_digit_contribution canonical := by
  intro pre post c p s d hp hs hd
  have hh := decode_int_horner_step (String.ofList pre) c p d hp hd
  have ht := decode_int_concat_homomorphism ((String.ofList pre) ++ String.singleton c)
    (String.ofList post) (p*58+d) s hh hs
  simpa [String.toList_singleton, ← String.ofList_append, String.singleton_eq_ofList,
    List.append_assoc, List.singleton_append, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm] using ht

theorem ones_prefix (z : Nat) (cs : List Char) :
    ((List.replicate z '1' ++ cs).takeWhile (· == '1')).length =
      z + (cs.takeWhile (· == '1')).length ∧
    (List.replicate z '1' ++ cs).dropWhile (· == '1') = cs.dropWhile (· == '1') := by
  induction z with
  | zero => simp
  | succ z ih => simp [List.replicate_succ, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem decode_leading_one_prefix_homomorphism : spec_decode_leading_one_prefix_homomorphism canonical := by
  intro z s
  change Base58.decode _ = _
  simp only [Base58.decode, String.toList_append, String.toList_ofList,
    (ones_prefix z s.toList).1, (ones_prefix z s.toList).2]
  cases hc : Base58.decodeInt (String.ofList (s.toList.dropWhile (· == '1'))) <;>
    simp [canonical, Base58.decode, hc, List.replicate_add, List.append_assoc, -List.replicate_append_replicate]

theorem be_fold_offset (cs : Bytes) (a b : Nat) :
    cs.foldl (fun acc b => acc * 256 + b) (a+b) =
      a * 256 ^ cs.length + cs.foldl (fun acc b => acc * 256 + b) b := by
  induction cs generalizing a b with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hh := ih (a*256) (b*256+c)
    rw [show (a+b)*256+c = a*256+(b*256+c) by ring, ih]
    simp only [Nat.pow_succ]
    ring

theorem be_append (left right : Bytes) :
    beValueGT (left ++ right) = beValueGT left * 256 ^ right.length + beValueGT right := by
  simp only [beValueGT, List.foldl_append]
  simpa using be_fold_offset right (beValueGT left) 0

theorem encode_append_big_endian_blocks : spec_encode_append_big_endian_blocks canonical := by
  intro z b left right hb
  have hh := encode_leading_zero_boundary z b (left ++ right) hb
  rw [← be_append]
  exact hh

theorem fold_mod57 (cs : List Char) (a n : Nat)
    (h : cs.foldl step (some a) = some n) :
    n % 57 = (a + (cs.map digitValueGT).sum) % 57 := by
  induction cs generalizing a n with
  | nil => simpa using congrArg (fun x => x % 57) (Option.some.inj h).symm
  | cons c cs ih =>
    cases hc : b58Idx c with
    | none => simp [List.foldl_cons, step, hc, fold_none] at h
    | some d =>
      have hh := ih (a*58+d) n (by simpa [List.foldl_cons, step, hc] using h)
      simpa [digitValueGT, hc, Nat.add_mod, Nat.mul_mod, Nat.add_assoc] using hh

theorem decode_int_digit_sum_mod57 : spec_decode_int_digit_sum_mod57 canonical := by
  intro s n _ h
  have hh := fold_mod57 s.toList 0 n h
  simpa [base58DigitSumGT, ← List.sum_eq_foldl_nat] using hh

end Base58Certificates
