import Aesop
import Lean.Elab.Tactic.Omega
import Cachetools.Spec.Lru
set_option maxRecDepth 256
set_option maxHeartbeats 2000
theorem canonical_spec_get_hit_mru : spec_get_hit_mru canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_get_hit_mru, canonical, Cachetools.contains, Cachetools.empty, Cachetools.get, Cachetools.lruKey, Cachetools.put]
  | solve | unfold spec_get_hit_mru; dsimp [canonical]; aesop
  | solve | unfold spec_get_hit_mru; dsimp [canonical]; intros; omega

#print axioms canonical_spec_get_hit_mru

theorem canonical_spec_get_miss_noop : spec_get_miss_noop canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_get_miss_noop, canonical, Cachetools.contains, Cachetools.empty, Cachetools.get, Cachetools.lruKey, Cachetools.put]
  | solve | unfold spec_get_miss_noop; dsimp [canonical]; aesop
  | solve | unfold spec_get_miss_noop; dsimp [canonical]; intros; omega

#print axioms canonical_spec_get_miss_noop

theorem canonical_spec_lruKey_last : spec_lruKey_last canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_lruKey_last, canonical, Cachetools.contains, Cachetools.empty, Cachetools.get, Cachetools.lruKey, Cachetools.put]
  | solve | unfold spec_lruKey_last; dsimp [canonical]; aesop
  | solve | unfold spec_lruKey_last; dsimp [canonical]; intros; omega

#print axioms canonical_spec_lruKey_last

theorem canonical_spec_empty_contains : spec_empty_contains canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_empty_contains, canonical, Cachetools.contains, Cachetools.empty, Cachetools.get, Cachetools.lruKey, Cachetools.put]
  | solve | unfold spec_empty_contains; dsimp [canonical]; aesop
  | solve | unfold spec_empty_contains; dsimp [canonical]; intros; omega

#print axioms canonical_spec_empty_contains

theorem canonical_spec_empty_capacity : spec_empty_capacity canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_empty_capacity, canonical, Cachetools.contains, Cachetools.empty, Cachetools.get, Cachetools.lruKey, Cachetools.put]
  | solve | unfold spec_empty_capacity; dsimp [canonical]; aesop
  | solve | unfold spec_empty_capacity; dsimp [canonical]; intros; omega

#print axioms canonical_spec_empty_capacity

theorem canonical_spec_empty_order : spec_empty_order canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_empty_order, canonical, Cachetools.contains, Cachetools.empty, Cachetools.get, Cachetools.lruKey, Cachetools.put]
  | solve | unfold spec_empty_order; dsimp [canonical]; aesop
  | solve | unfold spec_empty_order; dsimp [canonical]; intros; omega

#print axioms canonical_spec_empty_order

theorem canonical_spec_empty_lruKey : spec_empty_lruKey canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_empty_lruKey, canonical, Cachetools.contains, Cachetools.empty, Cachetools.get, Cachetools.lruKey, Cachetools.put]
  | solve | unfold spec_empty_lruKey; dsimp [canonical]; aesop
  | solve | unfold spec_empty_lruKey; dsimp [canonical]; intros; omega

#print axioms canonical_spec_empty_lruKey

theorem canonical_spec_contains_iff_mem : spec_contains_iff_mem canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_contains_iff_mem, canonical, Cachetools.contains, Cachetools.empty, Cachetools.get, Cachetools.lruKey, Cachetools.put]
  | solve | unfold spec_contains_iff_mem; dsimp [canonical]; aesop
  | solve | unfold spec_contains_iff_mem; dsimp [canonical]; intros; omega

#print axioms canonical_spec_contains_iff_mem

theorem canonical_spec_get_keeps_present : spec_get_keeps_present canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_get_keeps_present, canonical, Cachetools.contains, Cachetools.empty, Cachetools.get, Cachetools.lruKey, Cachetools.put]
  | solve | unfold spec_get_keeps_present; dsimp [canonical]; aesop
  | solve | unfold spec_get_keeps_present; dsimp [canonical]; intros; omega

#print axioms canonical_spec_get_keeps_present

theorem canonical_spec_lruKey_none_iff_empty : spec_lruKey_none_iff_empty canonical := by
  first
  | rfl
  | decide
  | solve | simp_all [spec_lruKey_none_iff_empty, canonical, Cachetools.contains, Cachetools.empty, Cachetools.get, Cachetools.lruKey, Cachetools.put]
  | solve | unfold spec_lruKey_none_iff_empty; dsimp [canonical]; aesop
  | solve | unfold spec_lruKey_none_iff_empty; dsimp [canonical]; intros; omega

#print axioms canonical_spec_lruKey_none_iff_empty
