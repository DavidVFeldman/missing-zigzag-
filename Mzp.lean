/-
  The Missing Zigzag
  ==================

  Lean 4 formalization accompanying the paper

      D. V. Feldman, "The Missing Zigzag: Cycles of Semitone Trichords
      and a Conservation Law in Equal Temperament."

  A *trichord cycle* in n-tone equal temperament is a cyclic word of
  n-3 pitch classes whose n-3 consecutive three-note windows realize,
  exactly once each, every trichord class {0,1,k} (2 <= k <= n-2)
  containing a semitone -- classes taken up to transposition only.
  Each cycle presents the chromatic class {0,1,2} either *scalarly*
  (consecutive steps equal, both +-1) or in *zigzag*.

  Main results:

    zigzag_three_dvd        a zigzag presentation forces 3 | n
                            (for interval cycles of ANY drift)
    cycle_zigzag_three_dvd  the same, for pitch cycles
    twelve_no_zigzag        no trichord cycle in 12TET is zigzag
    six_no_cycle            6TET admits no trichord cycle at all
    zigzag_classification   zigzag cycles exist iff 3 | n and n /= 12

  The primary formal object is the STEP WORD (interval cycle)
  `D : ZMod (n-3) -> ZMod n`, with windows the consecutive pairs
  `(D i, D (i+1))`; pitch cycles are recovered by differencing.  In
  this setting the conservation law is a telescoping identity: the
  proof uses no graph theory, no Eulerian circuits, and no multiset
  balance.

  This development is complete and declares no new axioms.  For the
  axiom profile of each result see `Audit.lean` and `docs/STATUS.md`.

  Copyright (c) 2026 David Victor Feldman.  Released under the
  Apache License, Version 2.0; see LICENSE.
-/
import Mathlib

namespace MZP

/- ==================== §1 DEFINITIONS ==================== -/

section
/-
  The Missing Zigzag — Lean 4 formalization, Phase 1: definitions.

  Primary objects are STEP WORDS (interval cycles), not pitch cycles:
  a cyclic word `D : ZMod (n-3) → ZMod n` of melodic steps whose
  consecutive pairs `(D i, D (i+1))` realize each semitone trichord
  class `{0,1,k}`, `2 ≤ k ≤ n-2`, exactly once.  Pitch cycles are the
  drift-0 special case, obtained by differencing.  This choice makes
  the conservation law (MzpConservation.lean) provable by telescoping,
  with no graph theory.

  Convention: classes are indexed by natural numbers k with
  2 ≤ k ≤ n - 2 (so `{0,1,n-1}` is identified with `{0,1,2}` by
  exclusion of k = n-1 from the range).  All subtraction on ℕ below is
  guarded by the standing hypothesis `6 ≤ n`.
-/


variable (n : ℕ)

/-- The ordered step pair `(a, b)` realizes the semitone trichord class
`k`: the three pitches `0, a, a+b` visited from any base are a translate
of `{0, 1, k}`. -/
def RealizesClass (k : ℕ) (a b : ZMod n) : Prop :=
  ∃ t : ZMod n, ({0, a, a + b} : Finset (ZMod n)) = {t, t + 1, t + (k : ZMod n)}

instance (k : ℕ) (a b : ZMod n) [NeZero n] : Decidable (RealizesClass n k a b) := by
  unfold RealizesClass; infer_instance

/-- An interval cycle (drift unrestricted): a cyclic step word of length
`n - 3` whose windows realize each class `k ∈ [2, n-2]` exactly once. -/
def IsIntervalCycle (D : ZMod (n - 3) → ZMod n) : Prop :=
  ∀ k ∈ Finset.Icc 2 (n - 2), ∃! i : ZMod (n - 3),
    RealizesClass n k (D i) (D (i + 1))

/-- Sum a function over a nontrivial finite cyclic group.  The zero-modulus
branch is included only to make the definition total; all applications below
have positive modulus. -/
noncomputable def cyclicSum {m : ℕ} {A : Type*} [AddCommMonoid A]
    (f : ZMod m → A) : A :=
  if hm : m = 0 then 0 else
    letI : NeZero m := ⟨hm⟩
    ∑ i : ZMod m, f i

/-- The drift of a step word. -/
noncomputable def drift (D : ZMod (n - 3) → ZMod n) : ZMod n :=
  cyclicSum D

/-- Window `i` is the chromatic window. -/
def ChromaticAt (D : ZMod (n - 3) → ZMod n) (i : ZMod (n - 3)) : Prop :=
  RealizesClass n 2 (D i) (D (i + 1))

/-- Scalar presentation: the chromatic window is a directed semitone run. -/
def IsScalar (D : ZMod (n - 3) → ZMod n) : Prop :=
  ∃ i, ChromaticAt n D i ∧ D (i + 1) = D i ∧ (D i = 1 ∨ D i = -1)

/-- Zigzag presentation: a chromatic window that is not a run. -/
def IsZigzag (D : ZMod (n - 3) → ZMod n) : Prop :=
  ∃ i, ChromaticAt n D i ∧ ¬ (D (i + 1) = D i ∧ (D i = 1 ∨ D i = -1))

/-- Pitch cycles: step words of pitch sequences; drift is automatically 0. -/
def stepsOf (c : ZMod (n - 3) → ZMod n) : ZMod (n - 3) → ZMod n :=
  fun i => c (i + 1) - c i

def IsCycle (c : ZMod (n - 3) → ZMod n) : Prop :=
  IsIntervalCycle n (stepsOf n c)

/-- (easy; telescoping over `ZMod (n-3)`). -/
theorem drift_stepsOf (hn : 6 ≤ n) (c : ZMod (n - 3) → ZMod n) :
    drift n (stepsOf n c) = 0 := by
  have hn3 : n - 3 ≠ 0 := by omega
  haveI : NeZero (n - 3) := ⟨hn3⟩
  unfold drift stepsOf cyclicSum
  simp [hn3]
  have hsum : (∑ i : ZMod (n - 3), c (i + 1)) = ∑ i : ZMod (n - 3), c i :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod (n - 3))) c
  rw [hsum, sub_self]

set_option maxHeartbeats 400000 in
/-- (the six-forms workhorse).  For `2 ≤ k ≤ n - 2` and `6 ≤ n`,
`(a,b)` realizes class `k` iff it is one of the six form pairs
I..VI = (1,k-1), (k,1-k), (-1,k), (k-1,-k), (-k,1), (1-k,-1).
Proof: case analysis on the six orderings of `{t, t+1, t+k}`. -/
theorem realizes_iff_form (hn : 6 ≤ n) (k : ℕ) (hk : 2 ≤ k ∧ k ≤ n - 2)
    (a b : ZMod n) :
    RealizesClass n k a b ↔
      (a, b) = ((1 : ZMod n), (k : ZMod n) - 1) ∨
      (a, b) = ((k : ZMod n), 1 - (k : ZMod n)) ∨
      (a, b) = (-1, (k : ZMod n)) ∨
      (a, b) = ((k : ZMod n) - 1, -(k : ZMod n)) ∨
      (a, b) = (-(k : ZMod n), (1 : ZMod n)) ∨
      (a, b) = (1 - (k : ZMod n), -1) := by
  have hk_lt_n : k < n := by omega
  have hk_pos : 0 < k := by omega
  have h1_lt_n : 1 < n := by omega
  haveI : Fact (1 < n) := ⟨h1_lt_n⟩
  have h1_ne_0 : (1 : ZMod n) ≠ 0 := by simp
  constructor
  · intro ⟨t, ht⟩
    have h0_in_lhs : (0 : ZMod n) ∈ ({0, a, a + b} : Finset (ZMod n)) := by simp
    have h0_in_rhs : (0 : ZMod n) ∈ ({t, t + 1, t + (k : ZMod n)} : Finset (ZMod n)) := by rw [← ht]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h0_in_rhs
    rcases h0_in_rhs with rfl | h0_in_rhs | h0_in_rhs
    · -- Case t = 0: {0, a, a+b} = {0, 1, k}
      simp at ht
      -- Now ht : {0, a, a + b} = {0, 1, k}
      -- Analyze a ∈ {0, 1, k}
      have ha_mem : a ∈ ({0, a, a + b} : Finset (ZMod n)) := by simp
      rw [ht] at ha_mem
      simp at ha_mem
      -- Analyze a + b ∈ {0, 1, k}
      have hab_mem : (a + b) ∈ ({0, a, a + b} : Finset (ZMod n)) := by simp
      rw [ht] at hab_mem
      simp at hab_mem
      -- k ≥ 2, k < n, so 0, 1, k are distinct
      have hcard : ({(0 : ZMod n), 1, (k : ZMod n)} : Finset (ZMod n)).card = 3 := by
        have h01 : (0 : ZMod n) ≠ 1 := by simp
        have h0k : (0 : ZMod n) ≠ (k : ZMod n) := fun h => by
          have : (k : ZMod n).val = (0 : ZMod n).val := by rw [h]
          simp at this
          have hmod : k % n = k := Nat.mod_eq_of_lt hk_lt_n
          rw [hmod] at this
          omega
        have h1k : (1 : ZMod n) ≠ (k : ZMod n) := by
          intro heq
          have hval : (k : ZMod n).val = (1 : ZMod n).val := congr_arg (·.val) heq.symm
          rw [ZMod.val_natCast] at hval
          simp [ZMod.val_one] at hval
          have hmod : k % n = k := Nat.mod_eq_of_lt hk_lt_n
          rw [hmod] at hval
          omega
        -- Now prove the cardinality
        norm_num [h01, h0k, h1k]
      -- LHS must have 3 elements too
      rw [← ht] at hcard
      -- If a = 0 or a + b = 0, the set has ≤ 2 elements, contradiction with hcard
      have ha_ne_0 : a ≠ 0 := by
        intro ha0; rw [ha0] at hcard
        have h1 : ({(0 : ZMod n), b} : Finset (ZMod n)).card ≤ 2 := Finset.card_insert_le _ _
        simp at hcard; linarith
      have hab_ne_0 : a + b ≠ 0 := by
        intro hab0; rw [hab0] at hcard
        have h1 : ({(0 : ZMod n), a} : Finset (ZMod n)).card ≤ 2 := Finset.card_insert_le _ _
        simp at hcard
        have h2 : ({(a : ZMod n), 0} : Finset (ZMod n)) = {(0 : ZMod n), a} := by ext; simp [or_comm]
        rw [h2] at hcard; linarith
      have hab_ne_a : a + b ≠ a := by
        intro haba
        have hb : b = 0 := by linear_combination haba
        simp [hb] at hcard
        have h1 : ({(0 : ZMod n), a} : Finset (ZMod n)).card ≤ 2 := Finset.card_insert_le _ _
        linarith
      -- From ha_mem, a = 1 or a = k
      rcases ha_mem with rfl | rfl | rfl
      · contradiction
      · -- a = 1: check a + b ∈ {0, 1, k}
        rcases hab_mem with h | h | h
        · contradiction
        · -- a + b = 1, so b = 0, contradiction
          exfalso; apply hab_ne_0; simp_all
        · -- a + b = k, so b = k - 1
          left; simp [show b = (k : ZMod n) - 1 from by { have : (1 : ZMod n) + b = k := h; linear_combination this } ]
      · -- a = k: check a + b ∈ {0, 1, k}
        rcases hab_mem with h | h | h
        · contradiction
        · -- a + b = 1, so b = 1 - k
          right; left; simp [show b = 1 - (k : ZMod n) from by { have : (k : ZMod n) + b = 1 := h; linear_combination this } ]
        · contradiction
    · -- Case t + 1 = 0: t = -1, {0, a, a+b} = {-1, 0, -1+k}
      have ht_eq : t = -1 := eq_neg_of_add_eq_zero_left (by rw [h0_in_rhs])
      rw [ht_eq] at ht
      simp at ht
      have hmk1 : (-1 : ZMod n) + (k : ZMod n) = (k : ZMod n) - 1 := by ring
      rw [hmk1] at ht
      have ha_mem : a ∈ ({0, a, a + b} : Finset (ZMod n)) := by simp
      rw [ht] at ha_mem; simp at ha_mem
      have hab_mem : (a + b) ∈ ({0, a, a + b} : Finset (ZMod n)) := by simp
      rw [ht] at hab_mem; simp at hab_mem
      have hn1 : (-1 : ZMod n) ≠ 0 := by simp
      have hkm1_ne_neg1 : ((k : ZMod n) - 1) ≠ -1 := by
        intro h; have h' : (k : ZMod n) = 0 := by linear_combination h
        have h'' : k % n = 0 := by
          have := congr_arg ZMod.val h'
          simp [ZMod.val_natCast] at this
          exact this
        have hmod : k % n = k := Nat.mod_eq_of_lt hk_lt_n
        omega
      have hcard : ({(0 : ZMod n), a, a + b} : Finset (ZMod n)).card = 3 := by
        have heq : ({(0 : ZMod n), a, a + b} : Finset (ZMod n)) = {-1, 0, (k : ZMod n) - 1} := ht
        rw [heq]
        have h_neg1_ne_0 : (-1 : ZMod n) ≠ 0 := by simp
        have h_neg1_ne_k1 : (-1 : ZMod n) ≠ (k : ZMod n) - 1 := hkm1_ne_neg1.symm
        have h0_ne_k1 : (0 : ZMod n) ≠ (k : ZMod n) - 1 := by
          intro h
          have hk1 : (k : ZMod n) = 1 := by
            have : (0 : ZMod n) + 1 = (k : ZMod n) - 1 + 1 := by rw [h]
            simp at this
            exact this.symm
          have : (k : ZMod n).val = (1 : ZMod n).val := by rw [hk1]
          simp [ZMod.val_one, ZMod.val_natCast] at this
          have hmod : k % n = k := Nat.mod_eq_of_lt hk_lt_n
          rw [hmod] at this
          omega
        norm_num [h_neg1_ne_0, h_neg1_ne_k1, h0_ne_k1]
      have ha_ne_0 : a ≠ 0 := by
        intro ha0; rw [ha0] at hcard
        simp at hcard
        have h1 : ({(0 : ZMod n), b} : Finset (ZMod n)).card ≤ 2 := Finset.card_insert_le _ _
        linarith
      have hab_ne_0 : a + b ≠ 0 := by
        intro hab0; rw [hab0] at hcard
        have h1 : ({(0 : ZMod n), a} : Finset (ZMod n)).card ≤ 2 := Finset.card_insert_le _ _
        simp at hcard
        have h2 : ({(a : ZMod n), 0} : Finset (ZMod n)) = {(0 : ZMod n), a} := by ext x; simp [or_comm]
        rw [h2] at hcard; linarith
      rcases ha_mem with rfl | rfl | rfl
      · rcases hab_mem with h | h | h
        · exfalso; rw [h] at hcard; simp at hcard
        · exfalso; rw [h] at hcard; simp at hcard
        · right; right; left
          have hb : b = (k : ZMod n) := by simpa using by linear_combination h
          simp [hb]
      · contradiction
      · rcases hab_mem with h | h | h
        · right; right; right; left
          have hb : b = -(k : ZMod n) := by simpa using by linear_combination h
          simp [hb]
        · exfalso; rw [h] at hcard; simp at hcard
          have hle : ({(↑k : ZMod n) - 1, (0 : ZMod n)} : Finset _).card ≤ 2 := Finset.card_insert_le _ _
          linarith
        · exfalso; rw [h] at hcard; simp at hcard
          have hle : ({(0 : ZMod n), (↑k : ZMod n) - 1} : Finset _).card ≤ 2 := Finset.card_insert_le _ _
          linarith
    · -- Case t + k = 0: t = -k, {0, a, a+b} = {-k, -k+1, 0}
      have ht_eq : t = -(k : ZMod n) := eq_neg_of_add_eq_zero_left (by rw [h0_in_rhs])
      rw [ht_eq] at ht
      simp at ht
      -- Now ht : {0, a, a + b} = {-k, -k + 1, 0}
      have h_negk_ne_0 : (-↑k : ZMod n) ≠ 0 := by
        intro h
        have : (k : ZMod n).val = (0 : ZMod n).val := by
          simp only [neg_eq_zero] at h
          rw [h]
        simp [ZMod.val_natCast] at this
        have hmod : k % n = k := Nat.mod_eq_of_lt hk_lt_n
        rw [hmod] at this
        omega
      have h_negk1_ne_negk : (-↑k : ZMod n) + 1 ≠ -↑k := by simp
      have hcard : ({(0 : ZMod n), a, a + b} : Finset (ZMod n)).card = 3 := by
        have : ({(0 : ZMod n), a, a + b} : Finset (ZMod n)) = {(-↑k : ZMod n), (-↑k : ZMod n) + 1, 0} := ht
        rw [this]
        have h0_ne_negk : (0 : ZMod n) ≠ -↑k := h_negk_ne_0.symm
        have h0_ne_negk1 : (0 : ZMod n) ≠ -↑k + 1 := by
          intro h
          have hk1 : (k : ZMod n) = 1 := by linear_combination h
          have : (k : ZMod n).val = (1 : ZMod n).val := by rw [hk1]
          simp [ZMod.val_one, ZMod.val_natCast] at this
          have hmod : k % n = k := Nat.mod_eq_of_lt hk_lt_n
          rw [hmod] at this
          omega
        have hnegk_ne_negk1 : (-↑k : ZMod n) ≠ -↑k + 1 := h_negk1_ne_negk.symm
        rw [Finset.card_eq_three]
        exact ⟨-↑k, -↑k + 1, 0, hnegk_ne_negk1, h_negk_ne_0, h0_ne_negk1.symm, rfl⟩
      have ha_ne_0 : a ≠ 0 := by
        intro ha0
        rw [ha0] at hcard
        simp at hcard
        have hle : ({(0 : ZMod n), b} : Finset (ZMod n)).card ≤ 2 := Finset.card_insert_le _ _
        linarith
      have hab_ne_0 : a + b ≠ 0 := by
        intro hab0
        rw [hab0] at hcard
        simp at hcard
        have h2 : ({(a : ZMod n), 0} : Finset (ZMod n)) = {(0 : ZMod n), a} := by ext x; simp [or_comm]
        rw [h2] at hcard
        have hle : ({(0 : ZMod n), a} : Finset (ZMod n)).card ≤ 2 := Finset.card_insert_le _ _
        linarith
      have ha_mem : a ∈ ({0, a, a + b} : Finset (ZMod n)) := by simp
      rw [ht] at ha_mem; simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem
      have hab_mem : (a + b) ∈ ({0, a, a + b} : Finset (ZMod n)) := by simp
      rw [ht] at hab_mem; simp only [Finset.mem_insert, Finset.mem_singleton] at hab_mem
      rcases ha_mem with h | h | h
      · -- a = -k
        rw [h] at hab_mem hcard hab_ne_0
        rcases hab_mem with h' | h' | h'
        · -- a + b = -k, so b = 0
          exfalso; have hb : b = 0 := by linear_combination h'
          rw [hb] at hcard; simp at hcard
          have hle : ({(0 : ZMod n), (-↑k : ZMod n)} : Finset (ZMod n)).card ≤ 2 := Finset.card_insert_le _ _
          linarith
        · -- a + b = -k + 1, so b = 1
          right; right; right; right; left
          exact Prod.ext h (by linear_combination h')
        · -- a + b = 0
          exfalso; rw [h'] at hab_ne_0; simp at hab_ne_0
      · -- a = -k + 1
        rw [h] at hab_mem hcard hab_ne_0
        rcases hab_mem with h' | h' | h'
        · -- a + b = -k, so b = -1
          right; right; right; right; right
          have ha : a = 1 - (k : ZMod n) := by rw [h]; ring
          exact Prod.ext ha (by linear_combination h')
        · -- a + b = -k + 1, so b = 0
          exfalso; have hb : b = 0 := by linear_combination h'
          rw [hb] at hcard; simp at hcard
          have hle : ({(0 : ZMod n), (-↑k + 1 : ZMod n)} : Finset (ZMod n)).card ≤ 2 := Finset.card_insert_le _ _
          linarith
        · -- a + b = 0
          exfalso; rw [h'] at hab_ne_0; simp at hab_ne_0
      · -- a = 0: contradiction
        contradiction
  · intro h
    have hins : ∀ x y z : ZMod n, ({x, y, z} : Finset (ZMod n)) = {x, z, y} :=
      fun x y z => congrArg (insert x) (Finset.pair_comm y z)
    have hswap : ∀ x y z : ZMod n, ({x, y, z} : Finset (ZMod n)) = {y, x, z} :=
      fun x y z => Finset.insert_comm x y {z}
    have hrev : ∀ x y z : ZMod n, ({x, y, z} : Finset (ZMod n)) = {z, y, x} := by
      intro x y z; rw [hins x y z, hswap x z y, hins z x y]
    have hrot : ∀ x y z : ZMod n, ({x, y, z} : Finset (ZMod n)) = {y, z, x} := by
      intro x y z; rw [hswap x y z, hins y x z]
    have hrot' : ∀ x y z : ZMod n, ({x, y, z} : Finset (ZMod n)) = {z, x, y} := by
      intro x y z; rw [hrot x y z, hrot y z x]
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨0, ?_⟩
      have e1 : (0 : ZMod n) + 1 = 1 := by ring
      have e2 : (0 : ZMod n) + (k : ZMod n) = (k : ZMod n) := by ring
      have e3 : (1 : ZMod n) + ((k : ZMod n) - 1) = (k : ZMod n) := by ring
      rw [e1, e2, e3]
    · refine ⟨0, ?_⟩
      have e1 : (0 : ZMod n) + 1 = 1 := by ring
      have e2 : (0 : ZMod n) + (k : ZMod n) = (k : ZMod n) := by ring
      have e3 : (k : ZMod n) + (1 - (k : ZMod n)) = 1 := by ring
      rw [e1, e2, e3]
      exact hins _ _ _
    · refine ⟨-1, ?_⟩
      have e1 : (-1 : ZMod n) + 1 = 0 := by ring
      have e2 : (-1 : ZMod n) + (k : ZMod n) = (k : ZMod n) - 1 := by ring
      rw [e1, e2]
      exact hswap _ _ _
    · refine ⟨-1, ?_⟩
      have e1 : (-1 : ZMod n) + 1 = 0 := by ring
      have e2 : (-1 : ZMod n) + (k : ZMod n) = (k : ZMod n) - 1 := by ring
      have e3 : ((k : ZMod n) - 1) + (-(k : ZMod n)) = -1 := by ring
      rw [e1, e2, e3]
      exact hrot' _ _ _
    · refine ⟨-(k : ZMod n), ?_⟩
      have e1 : (-(k : ZMod n)) + 1 = 1 - (k : ZMod n) := by ring
      have e2 : (-(k : ZMod n)) + (k : ZMod n) = 0 := by ring
      rw [e1, e2]
      exact hrot _ _ _
    · refine ⟨-(k : ZMod n), ?_⟩
      have e1 : (-(k : ZMod n)) + 1 = 1 - (k : ZMod n) := by ring
      have e2 : (-(k : ZMod n)) + (k : ZMod n) = 0 := by ring
      have e3 : (1 - (k : ZMod n)) + (-1 : ZMod n) = -(k : ZMod n) := by ring
      rw [e1, e2, e3]
      exact hrev _ _ _

/-- A step pair realizes at most one class in range.
Proof outline: rewrite both hypotheses with `realizes_iff_form`; this gives a
36-case cross-comparison of the two six-entry form lists at k and k'.
Each off-diagonal case yields a ZMod n equation among the casts of
1, -1, k, k-1, 1-k, -k, k', k'-1, 1-k', -k'; transfer to ℕ via `val`
(all the relevant values lie in [0, n)) and refute with `omega` using
2 ≤ k, k' ≤ n - 2.  Diagonal cases give (k : ZMod n) = (k' : ZMod n)
or ((k-1 : ...)) = ..., whence k = k' by `ZMod.val` injectivity on
[0, n).  Alternative set-theoretic route: both realizations give
{t, t+1, t+k} = {t', t'+1, t'+k'}; for k, k' ≥ 3 each side has a unique
ascending consecutive pair, forcing t = t' and then k = k'; the k = 2
cases are the three-term-run analysis.  Either route is acceptable. -/
theorem realizes_class_unique (hn : 6 ≤ n) {k k' : ℕ}
    (hk : 2 ≤ k ∧ k ≤ n - 2) (hk' : 2 ≤ k' ∧ k' ≤ n - 2)
    {a b : ZMod n} (h : RealizesClass n k a b)
    (h' : RealizesClass n k' a b) : k = k' := by
  have hklo : 2 ≤ k := hk.1
  have hkhi : k ≤ n - 2 := hk.2
  have hk'lo : 2 ≤ k' := hk'.1
  have hk'hi : k' ≤ n - 2 := hk'.2
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hkm1 : (k : ZMod n) - 1 = ((k - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have hk'm1 : (k' : ZMod n) - 1 = ((k' - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k')]
    norm_num
  have hnegk : -(k : ZMod n) = ((n - k : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : k ≤ n), ZMod.natCast_self]
    simp
  have hnegk' : -(k' : ZMod n) = ((n - k' : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : k' ≤ n), ZMod.natCast_self]
    simp
  have honek : (1 : ZMod n) - k = ((n + 1 - k : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : k ≤ n + 1)]
    push_cast
    rw [ZMod.natCast_self]
    ring
  have honek' : (1 : ZMod n) - k' = ((n + 1 - k' : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : k' ≤ n + 1)]
    push_cast
    rw [ZMod.natCast_self]
    ring
  have hnegone : (-1 : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]
    simp
  have hklt : k < n := by omega
  have hk'lt : k' < n := by omega
  have hkm1lt : k - 1 < n := by omega
  have hk'm1lt : k' - 1 < n := by omega
  have hnmklt : n - k < n := by omega
  have hnmk'lt : n - k' < n := by omega
  have honeklt : n + 1 - k < n := by omega
  have honek'lt : n + 1 - k' < n := by omega
  have hn1lt : n - 1 < n := by omega
  have sub_one_inj {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
      (e : x - 1 = y - 1) : x = y := by omega
  have nplus_sub_inj {x y : ℕ} (hx : x ≤ n - 2) (hy : y ≤ n - 2)
      (e : n + 1 - x = n + 1 - y) : x = y := by omega
  have n_sub_inj {x y : ℕ} (hx : x ≤ n - 2) (hy : y ≤ n - 2)
      (e : n - x = n - y) : x = y := by omega
  rw [realizes_iff_form n hn k hk] at h
  rw [realizes_iff_form n hn k' hk'] at h'
  simp only [hkm1, hk'm1, hnegk, hnegk', honek, honek', hnegone] at h h'
  rcases h with h | h | h | h | h | h <;>
    rcases h' with h' | h' | h' | h' | h' | h' <;>
    have heq : _ = _ := h.symm.trans h' <;>
    have e1 := congrArg (fun p : ZMod n × ZMod n => p.1.val) heq <;>
    have e2 := congrArg (fun p : ZMod n × ZMod n => p.2.val) heq <;>
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hklt,
      Nat.mod_eq_of_lt hk'lt, Nat.mod_eq_of_lt hkm1lt,
      Nat.mod_eq_of_lt hk'm1lt, Nat.mod_eq_of_lt hnmklt,
      Nat.mod_eq_of_lt hnmk'lt, Nat.mod_eq_of_lt honeklt,
      Nat.mod_eq_of_lt honek'lt, Nat.mod_eq_of_lt hn1lt] at e1 e2 <;>
    try simp only [ZMod.val_one] at e1 e2
  all_goals first
    | exact e1
    | exact nplus_sub_inj hkhi hk'hi e1
    | exact n_sub_inj hkhi hk'hi e1
    | exact n_sub_inj hkhi hk'hi e2
    | exact sub_one_inj hklo hk'lo e1
    | exact sub_one_inj hklo hk'lo e2
    | omega

/-- Every window realizes some class (pigeonhole).
Proof outline: `hD` gives, for each of the `n - 3` classes, a unique position;
`realizes_class_unique` makes the induced map classes → positions
injective (two classes at one position would coincide).  Since
`(Finset.Icc 2 (n-2)).card = n - 3 = Fintype.card (ZMod (n-3))`
(here `6 ≤ n` gives `NeZero (n-3)`), the map is surjective
(`Finset.surj_on_of_inj_on_of_card_le` or build an `Equiv` via
`Fintype.bijective_iff_injective_and_card`), so every position receives
a class. -/
theorem exists_class_at (hn : 6 ≤ n) (D : ZMod (n - 3) → ZMod n)
    (hD : IsIntervalCycle n D) (i : ZMod (n - 3)) :
    ∃ k ∈ Finset.Icc 2 (n - 2), RealizesClass n k (D i) (D (i + 1)) := by
  classical
  haveI : NeZero (n - 3) := ⟨by omega⟩
  by_contra hcon
  push_neg at hcon
  set S : Finset ℕ := Finset.Icc 2 (n - 2) with hS
  have hcardS : S.card = n - 3 := by
    rw [hS, Nat.card_Icc]; omega
  set P : ℕ → ZMod (n - 3) :=
    fun k => if h : k ∈ S then (hD k h).choose else 0 with hPdef
  have hPspec : ∀ k (h : k ∈ S),
      RealizesClass n k (D (P k)) (D (P k + 1)) := by
    intro k h
    simp only [hPdef, dif_pos h]
    exact (hD k h).choose_spec.1
  have hne : ∀ k ∈ S, P k ≠ i := by
    intro k hk hEq
    exact hcon k hk (hEq ▸ hPspec k hk)
  have hmap : ∀ k ∈ S, P k ∈ Finset.univ.erase i := by
    intro k hk
    exact Finset.mem_erase.mpr ⟨hne k hk, Finset.mem_univ _⟩
  have hinj : ∀ k₁ ∈ S, ∀ k₂ ∈ S, P k₁ = P k₂ → k₁ = k₂ := by
    intro k₁ h₁ k₂ h₂ he
    exact realizes_class_unique n hn
      (Finset.mem_Icc.mp h₁) (Finset.mem_Icc.mp h₂)
      (hPspec k₁ h₁) (he ▸ hPspec k₂ h₂)
  have hcard := Finset.card_le_card_of_injOn (s := S) (t := Finset.univ.erase i) P
    (fun k hk => Finset.mem_coe.mpr (hmap k (Finset.mem_coe.mp hk)))
    (fun k₁ h₁ k₂ h₂ he => hinj k₁ (Finset.mem_coe.mp h₁) k₂ (Finset.mem_coe.mp h₂) he)
  rw [hcardS, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, ZMod.card] at hcard
  omega

/-- (chromatic cadence lemma; LOWER PRIORITY, standalone).
Proof outline: with `exists_class_at` (the corresponding step) get a class k realized at
window i.  If the signs are opposite, `b = -a` so the window set
`{0, a, a + b} = {0, a, 0}` has card ≤ 2, while the realizing set
`{t, t+1, t+k}` has card 3 (its three elements are pairwise distinct
for 2 ≤ k ≤ n-2 < n): contradiction.  If the signs agree, exhibit the
chromatic translate directly: for a = 1 take t = 0, for a = -1 take
t = -2; conclude `D (i+1) = D i` and `ChromaticAt`. -/
theorem adjacent_semitones (hn : 6 ≤ n) (D : ZMod (n - 3) → ZMod n)
    (hD : IsIntervalCycle n D) (i : ZMod (n - 3))
    (h1 : D i = 1 ∨ D i = -1) (h2 : D (i + 1) = 1 ∨ D (i + 1) = -1) :
    D (i + 1) = D i ∧ ChromaticAt n D i := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  obtain ⟨k, hkmem, hk⟩ := exists_class_at n hn D hD i
  rw [Finset.mem_Icc] at hkmem
  have hform := (realizes_iff_form n hn k ⟨hkmem.1, hkmem.2⟩ _ _).mp hk
  -- natCast normal forms
  have hone : (1 : ZMod n) = ((1 : ℕ) : ZMod n) := by simp
  have hnegone : (-1 : ZMod n) = ((n - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), ZMod.natCast_self]; simp
  have hkm1 : (k : ZMod n) - 1 = ((k - 1 : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
  have hnegk : -(k : ZMod n) = ((n - k : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : k ≤ n), ZMod.natCast_self]; simp
  have honek : (1 : ZMod n) - k = ((n + 1 - k : ℕ) : ZMod n) := by
    rw [Nat.cast_sub (by omega : k ≤ n + 1)]; push_cast; rw [ZMod.natCast_self]; ring
  have hvals : ∀ m : ℕ, m < n → (((m : ℕ) : ZMod n)).val = m := by
    intro m hm; rw [ZMod.val_natCast, Nat.mod_eq_of_lt hm]
  have v_one : (1 : ZMod n).val = 1 := by
    rw [hone, hvals 1 (by omega)]
  have v_negone : (-1 : ZMod n).val = n - 1 := by
    rw [hnegone, hvals _ (by omega)]
  have v_k : ((k : ℕ) : ZMod n).val = k := hvals k (by omega)
  have v_km1 : ((k : ZMod n) - 1).val = k - 1 := by
    rw [hkm1, hvals _ (by omega)]
  have v_1mk : ((1 : ZMod n) - (k : ZMod n)).val = n + 1 - k := by
    rw [honek, hvals _ (by omega)]
  have v_negk : (-(k : ZMod n)).val = n - k := by
    rw [hnegk, hvals _ (by omega)]
  -- the two steps have equal sign
  have hsame : (D i = 1 ∧ D (i + 1) = 1) ∨ (D i = -1 ∧ D (i + 1) = -1) := by
    rcases h1 with ha | ha <;> rcases h2 with hb | hb
    · exact Or.inl ⟨ha, hb⟩
    · exfalso
      rw [ha, hb] at hform
      rcases hform with h' | h' | h' | h' | h' | h' <;>
      · rw [Prod.mk.injEq] at h'
        have v1 := congrArg ZMod.val h'.1
        have v2 := congrArg ZMod.val h'.2
        simp only [v_one, v_negone, v_k, v_km1, v_1mk, v_negk] at v1 v2
        omega
    · exfalso
      rw [ha, hb] at hform
      rcases hform with h' | h' | h' | h' | h' | h' <;>
      · rw [Prod.mk.injEq] at h'
        have v1 := congrArg ZMod.val h'.1
        have v2 := congrArg ZMod.val h'.2
        simp only [v_one, v_negone, v_k, v_km1, v_1mk, v_negk] at v1 v2
        omega
    · exact Or.inr ⟨ha, hb⟩
  have h2mem : 2 ≤ 2 ∧ 2 ≤ n - 2 := ⟨le_refl 2, by omega⟩
  rcases hsame with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨by rw [ha, hb], ?_⟩
    show RealizesClass n 2 (D i) (D (i + 1))
    rw [realizes_iff_form n hn 2 h2mem _ _, ha, hb]
    left
    have : ((2 : ℕ) : ZMod n) - 1 = 1 := by push_cast; ring
    rw [this]
  · refine ⟨by rw [ha, hb], ?_⟩
    show RealizesClass n 2 (D i) (D (i + 1))
    rw [realizes_iff_form n hn 2 h2mem _ _, ha, hb]
    right; right; right; right; right
    have : (1 : ZMod n) - ((2 : ℕ) : ZMod n) = -1 := by push_cast; ring
    rw [this]
end

/- ==================== §2 THE CONSERVATION LAW ==================== -/

section
/-
  Phase 1 flagship: the conservation law (paper Theorem 6.1), stated for
  interval cycles of ARBITRARY drift — the proof never uses closure.

  Architecture (no graph theory needed):
    * weight  w : ZMod n → ZMod 3
    * per-window invariance: for 3 ≤ k ≤ n-2, every form of class k
      contributes  w b - w a ≡ n + k - 2  (mod 3)
    * chromatic contribution: scalar forms give 0, zigzag give ±n

    * telescoping: ∑ᵢ (w (D (i+1)) - w (D i)) = 0
    * Gauss sum: ∑_{k=3}^{n-2} (n+k-2) ≡ 0 (mod 3)
    * assembly via the position↔class bijection
-/


variable (n : ℕ)

/-- The weight.  `w 1 = 0`, `w (-1) = 1`, and `w j = n + j - 1 (mod 3)`
for interior `j` (i.e. `2 ≤ j.val ≤ n - 2`). -/
def w : ZMod n → ZMod 3 :=
  fun x => if x = 1 then 0 else if x = -1 then 1 else ((n + x.val - 1 : ℕ) : ZMod 3)

lemma w_one (hn : 3 ≤ n) : w n (1 : ZMod n) = 0 := by
  simp [w]

lemma w_neg_one (hn : 3 ≤ n) : w n (-1 : ZMod n) = 1 := by
  haveI : Fact (2 < n) := ⟨by omega⟩
  simp [w, ZMod.neg_one_ne_one]

lemma w_natCast_interior (hn : 6 ≤ n) (k : ℕ) (hk : 3 ≤ k ∧ k ≤ n - 2) :
    w n (k : ZMod n) = ((n + k - 1 : ℕ) : ZMod 3) := by
  rw [w]
  have hk_lt_n : k < n := Nat.lt_of_le_of_lt hk.2 (Nat.sub_lt (by linarith) (by linarith))
  haveI : Fact (1 < n) := ⟨by linarith⟩
  have h1 : ¬((k : ZMod n) = 1) := by
    intro heq
    have hval := congr_arg ZMod.val heq
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk_lt_n, ZMod.val_one] at hval
    omega
  have h2 : ¬((k : ZMod n) = -1) := by
    intro heq
    have hval := congr_arg ZMod.val heq
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hk_lt_n] at hval
    rcases n with _ | _ | n
    · contradiction
    · contradiction
    · simp_all [ZMod.val_neg_one]
  simp [h1, h2, Nat.mod_eq_of_lt hk_lt_n]

lemma w_natCast_sub_one (hn : 6 ≤ n) (k : ℕ) (hk : 3 ≤ k ∧ k ≤ n - 2) :
    w n ((k : ZMod n) - 1) = ((n + k - 2 : ℕ) : ZMod 3) := by
  have hk_lt_n : k < n := by omega
  simp [w]
  have h1 : (k : ZMod n) - 1 ≠ 1 := by
    intro heq
    have : (k : ZMod n) = 2 := by linear_combination heq
    have hval : (k : ZMod n).val = (2 : ZMod n).val := congr_arg ZMod.val this
    rw [ZMod.val_natCast] at hval
    simp [ZMod.val_ofNat] at hval
    have hmod : k % n = k := Nat.mod_eq_of_lt hk_lt_n
    have hmod2 : 2 % n = 2 := Nat.mod_eq_of_lt (by omega : 2 < n)
    rw [hmod, hmod2] at hval
    omega
  have h2 : (k : ZMod n) ≠ 0 := by
    intro heq
    have hval : (k : ZMod n).val = 0 := by rw [heq]; exact ZMod.val_zero
    rw [ZMod.val_natCast] at hval
    have hmod : k % n = k := Nat.mod_eq_of_lt hk_lt_n
    rw [hmod] at hval
    omega
  rw [if_neg h1, if_neg h2]
  have hval : ((k : ZMod n) - 1).val = k - 1 := by
    have h1' : (k : ZMod n) - 1 = ((k - 1 : ℕ) : ZMod n) := by
      have hge : 1 ≤ k := by omega
      simp [Nat.cast_sub hge]
    rw [h1']
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : k - 1 < n)]
  rw [hval]
  congr 1
  omega

lemma w_neg_natCast (hn : 6 ≤ n) (k : ℕ) (hk : 3 ≤ k ∧ k ≤ n - 2) :
    w n (-(k : ZMod n)) = ((2 * n - k - 1 : ℕ) : ZMod 3) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  rw [w]
  have hk_lt_n : k < n := by omega
  have h_neg1_val : (-1 : ZMod n).val = n - 1 := by
    have : (-1 : ZMod n) = (n - 1 : ℕ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      simp
    rw [this, ZMod.val_natCast]
    simp [Nat.mod_eq_of_lt (by omega : n - 1 < n)]
  have h_ne_1 : (-(k : ZMod n)) ≠ 1 := by
    intro heq
    have heq2 : (k : ZMod n) = -1 := by linear_combination -heq
    have hval : (k : ZMod n).val = (-1 : ZMod n).val := congr_arg ZMod.val heq2
    rw [ZMod.val_natCast, h_neg1_val] at hval
    rw [Nat.mod_eq_of_lt hk_lt_n] at hval
    omega
  have h_ne_neg1 : (-(k : ZMod n)) ≠ -1 := by
    intro heq
    have heq2 : (k : ZMod n) = 1 := by linear_combination -heq
    have hval : (k : ZMod n).val = (1 : ZMod n).val := congr_arg ZMod.val heq2
    rw [ZMod.val_natCast, ZMod.val_one] at hval
    rw [Nat.mod_eq_of_lt hk_lt_n] at hval
    omega
  rw [if_neg h_ne_1, if_neg h_ne_neg1]
  congr 1
  have hval : (-(k : ZMod n)).val = n - k := by
    rw [show -(k : ZMod n) = ((n - k : ℕ) : ZMod n) by simp [hk_lt_n.le]]
    simp [Nat.mod_eq_of_lt (by omega : n - k < n)]
  rw [hval]
  omega

lemma w_one_sub_natCast (hn : 6 ≤ n) (k : ℕ) (hk : 3 ≤ k ∧ k ≤ n - 2) :
    w n (1 - (k : ZMod n)) = ((2 * n - k : ℕ) : ZMod 3) := by
  unfold w
  have hk_pos : 0 < k := by omega
  have hk_lt_n : k < n := by omega
  have h1 : (1 - (k : ZMod n)) ≠ 1 := by
    intro h
    have : (k : ZMod n) = 0 := by simp_all
    have := congr_arg ZMod.val this
    simp [ZMod.val_natCast] at this
    have hmod : k % n = k := Nat.mod_eq_of_lt hk_lt_n
    omega
  have h2 : (1 - (k : ZMod n)) ≠ -1 := by
    intro h
    have heq : (k : ZMod n) = 2 := by
      calc (k : ZMod n) = 1 - (1 - (k : ZMod n)) := by ring
        _ = 1 - (-1) := by rw [h]
        _ = 2 := by ring
    have := congr_arg ZMod.val heq
    simp only [ZMod.val_natCast] at this
    have hn2 : n > 2 := by omega
    have hval2 : ZMod.val (2 : ZMod n) = 2 := by
      cases n with
      | zero => contradiction
      | succ m => simp [ZMod.val]; omega
    have hmod : k % n = k := Nat.mod_eq_of_lt hk_lt_n
    omega
  simp [h1, h2]
  -- Now need to show: n + (1 - k).val - 1 = 2n - k
  -- (1 - k).val = n - (k - 1) = n - k + 1 when k ≥ 1 and k < n
  have hval : (1 - (k : ZMod n)).val = n - k + 1 := by
    have hn_zero : n ≠ 0 := by omega
    haveI : NeZero n := ⟨hn_zero⟩
    have h_eq : (1 - (k : ZMod n)) = -(k - 1 : ZMod n) := by ring
    rw [h_eq]
    have hk1_ne : (k - 1 : ZMod n) ≠ 0 := by
      intro h
      have : (k : ZMod n) = 1 := by linear_combination h
      have hval := congr_arg ZMod.val this
      simp [ZMod.val_natCast] at hval
      -- hval : k = ZMod.val 1
      have hn1 : n > 1 := by omega
      cases n with
      | zero => contradiction
      | succ m =>
        simp [ZMod.val] at hval
        have h1mod : 1 % (m + 1) = 1 := Nat.mod_eq_of_lt (by omega : 1 < m + 1)
        rw [h1mod] at hval
        have hval' : k = 1 := by
          have := Nat.mod_eq_of_lt hk_lt_n
          rw [this] at hval
          exact hval
        omega
    rw [ZMod.neg_val]
    simp [hk1_ne]
    have hk1_lt_n : k - 1 < n := by omega
    have hk1_pos : k - 1 ≥ 0 := Nat.zero_le _
    have hval_k1 : (↑k - 1 : ZMod n).val = k - 1 := by
      have : (↑k - 1 : ZMod n) = ↑(k - 1) := by
        simp [Nat.cast_sub hk_pos]
      rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt hk1_lt_n]
    rw [hval_k1]
    omega
  rw [hval]
  have : n + (n - k + 1) - 1 = 2 * n - k := by omega
  simp [this]

lemma contribution_arith_II (n k : ℕ) (hn : 6 ≤ n) (hk : 3 ≤ k) (h : k ≤ n) :
    ((2 * n - k : ℕ) : ZMod 3) - ((n + k - 1 : ℕ) : ZMod 3) =
      ((n + k - 2 : ℕ) : ZMod 3) := by
  have h1 : k ≤ 2 * n := by linarith
  have h2 : 2 ≤ n + k := by linarith
  have h3 : 1 ≤ n + k := by linarith
  rw [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
  ring_nf
  simp only [Nat.cast_add, Nat.cast_mul]
  ring_nf
  -- Goal: 1 + (↑n - ↑k * 2) = -2 + ↑n + ↑k in ZMod 3
  -- Rearrange: 3 = 3k, which is 0 = 0 in ZMod 3
  have h3 : (3 : ZMod 3) = 0 := by rfl
  calc 1 + ((n : ZMod 3) - k * 2)
      = 1 + n - 2 * k := by ring
    _ = -2 + n + k + (3 - 3 * k) := by ring
    _ = -2 + n + k + 3 * (1 - k) := by ring
    _ = -2 + n + k + 0 := by simp [h3]
    _ = -2 + (n + k) := by ring
    _ = -2 + n + k := by ring

lemma contribution_arith_III (n k : ℕ) (hn : 6 ≤ n) (hk : 3 ≤ k) :
    ((n + k - 1 : ℕ) : ZMod 3) - 1 = ((n + k - 2 : ℕ) : ZMod 3) := by
  have hge : n + k ≥ 2 := by omega
  rw [show n + k - 1 = (n + k - 2) + 1 by omega]
  rw [Nat.cast_add, Nat.cast_one]
  ring

lemma contribution_arith_IV (n k : ℕ) (hn : 6 ≤ n) (hk : 3 ≤ k) (hkn : k ≤ n) (h : k + 1 ≤ 2 * n) :
    ((2 * n - k - 1 : ℕ) : ZMod 3) - ((n + k - 2 : ℕ) : ZMod 3) =
      ((n + k - 2 : ℕ) : ZMod 3) := by
  have h1 : (2 * n - k - 1 + (n + k - 2) : ℕ) = 3 * (n - 1) := by omega
  have h2 : ((2 * n - k - 1 : ℕ) : ZMod 3) + ((n + k - 2 : ℕ) : ZMod 3) = 0 := by
    rw [← Nat.cast_add, h1]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [mul_eq_zero]
    left
    exact ZMod.natCast_self 3
  have h3 : ((2 * n - k - 1 : ℕ) : ZMod 3) = -((n + k - 2 : ℕ) : ZMod 3) := by
    rw [eq_neg_iff_add_eq_zero]
    exact h2
  rw [h3]
  ring_nf
  have : (2 : ZMod 3) = -1 := by rfl
  simp [this]

lemma contribution_arith_V (n k : ℕ) (hn : 6 ≤ n) (hk : 3 ≤ k) (hkn : k ≤ n) (h : k + 1 ≤ 2 * n) :
    0 - ((2 * n - k - 1 : ℕ) : ZMod 3) = ((n + k - 2 : ℕ) : ZMod 3) := by
  have h1 : (2 * n - k - 1 + (n + k - 2) : ℕ) = 3 * (n - 1) := by
    have hk1 : k + 1 ≤ 2 * n := h
    have hn1 : 1 ≤ n := by omega
    have h2 : 2 * n - (k + 1) + (n + k - 2) = 3 * (n - 1) := by omega
    convert h2 using 1
  have h2 : ((2 * n - k - 1 : ℕ) : ZMod 3) + ((n + k - 2 : ℕ) : ZMod 3) = 0 := by
    rw [← Nat.cast_add, h1]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [mul_eq_zero]
    left
    exact ZMod.natCast_self 3
  have h3 : -((2 * n - k - 1 : ℕ) : ZMod 3) = ((n + k - 2 : ℕ) : ZMod 3) := by
    rw [neg_eq_iff_add_eq_zero]
    exact h2
  rw [sub_eq_neg_add]
  simp [h3]

lemma contribution_arith_VI (n k : ℕ) (hn : 6 ≤ n) (hk : 3 ≤ k) (hkn : k ≤ n) (h : k ≤ 2 * n) :
    1 - ((2 * n - k : ℕ) : ZMod 3) = ((n + k - 2 : ℕ) : ZMod 3) := by
  have h1 : (2 * n - k : ℕ) = (2 * n - k - 1) + 1 := by omega
  rw [h1, Nat.cast_add]
  have hbase := contribution_arith_V n k hn hk hkn (by omega)
  linear_combination hbase

lemma w_two (hn : 6 ≤ n) : w n (2 : ZMod n) = ((n + 1 : ℕ) : ZMod 3) := by
  --
  haveI : Fact (1 < n) := ⟨by omega⟩
  have h1 : (2 : ZMod n) ≠ 1 := by
    intro h
    have h0 : (1 : ZMod n) = 0 := by linear_combination h
    exact one_ne_zero h0
  have h2 : (2 : ZMod n) ≠ -1 := by
    intro h
    have h30 : ((3 : ℕ) : ZMod n) = 0 := by push_cast; linear_combination h
    have hv := congrArg ZMod.val h30
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 3 < n)] at hv
    simp at hv
  have hval : (2 : ZMod n).val = 2 := by
    have h := ZMod.val_natCast (n := n) 2
    rw [Nat.mod_eq_of_lt (by omega)] at h
    exact_mod_cast h
  simp only [w, if_neg h1, if_neg h2, hval]
  congr 1

lemma w_neg_two (hn : 6 ≤ n) : w n (-2 : ZMod n) = ((2 * n - 3 : ℕ) : ZMod 3) := by
  --
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hkey : (-2 : ZMod n) = ((n - 2 : ℕ) : ZMod n) := by
    have hself : ((n : ℕ) : ZMod n) = 0 := ZMod.natCast_self n
    rw [Nat.cast_sub (by omega : 2 ≤ n), hself]
    ring
  have h1 : (-2 : ZMod n) ≠ 1 := by
    intro h
    have h30 : ((3 : ℕ) : ZMod n) = 0 := by push_cast; linear_combination -h
    have hv := congrArg ZMod.val h30
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 3 < n)] at hv
    simp at hv
  have h2 : (-2 : ZMod n) ≠ -1 := by
    intro h
    have h0 : (1 : ZMod n) = 0 := by linear_combination -h
    exact one_ne_zero h0
  have hval : (-2 : ZMod n).val = n - 2 := by
    rw [hkey]
    have h := ZMod.val_natCast (n := n) (n - 2)
    rw [Nat.mod_eq_of_lt (by omega)] at h
    exact h
  simp only [w, if_neg h1, if_neg h2, hval]
  congr 1
  omega

/-- All six forms of class `k ≥ 3` have the same weighted
contribution.  Pure case computation; the six entries of the form table
are interior for 3 ≤ k ≤ n-2, so `w` evaluates by its third branch
except at the literal entries 1 and -1. -/
theorem form_contribution (hn : 6 ≤ n) (k : ℕ) (hk : 3 ≤ k ∧ k ≤ n - 2)
    (a b : ZMod n) (h : RealizesClass n k a b) :
    w n b - w n a = ((n + k - 2 : ℕ) : ZMod 3) := by
  have hn3 : 3 ≤ n := by omega
  have hk2 : 2 ≤ k ∧ k ≤ n - 2 := ⟨by omega, hk.2⟩
  rw [@realizes_iff_form n hn k hk2] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- Form I: (a, b) = (1, k - 1)
    rw [@w_one n hn3]
    simp
    exact @w_natCast_sub_one n hn k hk
  · -- Form II: (a, b) = (k, 1 - k)
    rw [@w_natCast_interior n hn k hk, @w_one_sub_natCast n hn k hk]
    exact contribution_arith_II n k hn hk.1 (by omega)
  · -- Form III: (a, b) = (-1, k)
    rw [@w_neg_one n hn3, @w_natCast_interior n hn k hk]
    exact contribution_arith_III n k hn hk.1
  · -- Form IV: (a, b) = (k - 1, -k)
    rw [@w_natCast_sub_one n hn k hk, @w_neg_natCast n hn k hk]
    have hkn : k ≤ n := by omega
    exact contribution_arith_IV n k hn hk.1 hkn (by omega)
  · -- Form V: (a, b) = (-k, 1)
    rw [@w_neg_natCast n hn k hk, @w_one n hn3]
    have hkn : k ≤ n := by omega
    exact contribution_arith_V n k hn hk.1 hkn (by omega)
  · -- Form VI: (a, b) = (1 - k, -1)
    rw [@w_one_sub_natCast n hn k hk, @w_neg_one n hn3]
    have hkn : k ≤ n := by omega
    exact contribution_arith_VI n k hn hk.1 hkn (by omega)

/-- The chromatic contributes 0 if scalar, ±(n : ZMod 3) if
zigzag (sign by form). -/
theorem chromatic_contribution (hn : 6 ≤ n) (a b : ZMod n)
    (h : RealizesClass n 2 a b) :
    (b = a ∧ (a = 1 ∨ a = -1) ∧ w n b - w n a = 0) ∨
    (¬ (b = a ∧ (a = 1 ∨ a = -1)) ∧
      (w n b - w n a = (n : ZMod 3) ∨ w n b - w n a = -(n : ZMod 3))) := by
  --
  have hn3 : 3 ≤ n := by omega
  haveI : Fact (1 < n) := ⟨by omega⟩
  have h3ne : ((3 : ℕ) : ZMod n) ≠ 0 := by
    intro h30
    have hv := congrArg ZMod.val h30
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : 3 < n)] at hv
    simp at hv
  have hk2 : 2 ≤ 2 ∧ 2 ≤ n - 2 := ⟨le_refl 2, by omega⟩
  rw [@realizes_iff_form n hn 2 hk2] at h
  have hcast2 : ((2 : ℕ) : ZMod n) = (2 : ZMod n) := by push_cast; ring
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- Form I: (1, 2-1): scalar ascending
    left
    refine ⟨by push_cast; ring, Or.inl rfl, ?_⟩
    rw [show ((2 : ℕ) : ZMod n) - 1 = (1 : ZMod n) by push_cast; ring, @w_one n hn3]
    ring
  · -- Form II: (2, 1-2): zigzag, contribution -n
    right
    refine ⟨?_, Or.inr ?_⟩
    · rintro ⟨hba, -⟩
      exact h3ne (by push_cast; linear_combination -hba)
    · rw [show (1 - ((2 : ℕ) : ZMod n) : ZMod n) = (-1 : ZMod n) by push_cast; ring,
          @w_neg_one n hn3, hcast2, @w_two n hn]
      push_cast
      ring
  · -- Form III: (-1, 2): zigzag, contribution +n
    right
    refine ⟨?_, Or.inl ?_⟩
    · rintro ⟨hba, -⟩
      exact h3ne (by push_cast; linear_combination hba)
    · rw [hcast2, @w_two n hn, @w_neg_one n hn3]
      push_cast
      ring
  · -- Form IV: (2-1, -2): zigzag, contribution -n
    right
    refine ⟨?_, Or.inr ?_⟩
    · rintro ⟨hba, -⟩
      exact h3ne (by push_cast; linear_combination -hba)
    · rw [show ((2 : ℕ) : ZMod n) - 1 = (1 : ZMod n) by push_cast; ring,
          @w_one n hn3, show (-((2 : ℕ) : ZMod n) : ZMod n) = (-2 : ZMod n) by push_cast; ring,
          @w_neg_two n hn]
      rw [Nat.cast_sub (by omega : 3 ≤ 2 * n)]
      push_cast
      have hthree : ((3 : ℕ) : ZMod 3) = 0 := by decide
      linear_combination ((n : ZMod 3) - 1) * hthree
  · -- Form V: (-2, 1): zigzag, contribution +n
    right
    refine ⟨?_, Or.inl ?_⟩
    · rintro ⟨hba, -⟩
      exact h3ne (by push_cast; linear_combination hba)
    · rw [@w_one n hn3, show (-((2 : ℕ) : ZMod n) : ZMod n) = (-2 : ZMod n) by push_cast; ring,
          @w_neg_two n hn]
      rw [Nat.cast_sub (by omega : 3 ≤ 2 * n)]
      push_cast
      have hthree : ((3 : ℕ) : ZMod 3) = 0 := by decide
      linear_combination (1 - (n : ZMod 3)) * hthree
  · -- Form VI: (1-2, -1): scalar descending
    left
    refine ⟨by push_cast; ring, Or.inr (by push_cast; ring), ?_⟩
    rw [show (1 - ((2 : ℕ) : ZMod n) : ZMod n) = (-1 : ZMod n) by push_cast; ring,
        @w_neg_one n hn3]
    ring

/-- Telescoping around the cycle. -/
theorem telescope (hn : 6 ≤ n) (D : ZMod (n - 3) → ZMod n) :
    cyclicSum (fun i : ZMod (n - 3) => w n (D (i + 1)) - w n (D i)) = 0 := by
  unfold cyclicSum
  split
  · rfl
  · haveI : NeZero (n - 3) := ⟨by simp_all⟩
    simp only
    rw [Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    rw [← Equiv.sum_comp (Equiv.addRight (-1 : ZMod (n - 3)))]
    simp

/-- The fixed fee sum vanishes mod 3 for every n.
Closed form: (n-4)(n-2) + (n-2)(n-1)/2 - 3; verify by n % 3 cases. -/
theorem fee_sum (hn : 6 ≤ n) :
    ((∑ k ∈ Finset.Icc 3 (n - 2), (n + k - 2) : ℕ) : ZMod 3) = 0 := by
  -- We prove by showing the sum mod 3 is 0 using case analysis on n % 3
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  -- S(6) = 15 ≡ 0 (mod 3), and S(m+1) = S(m) + 3(m-2) ≡ S(m) (mod 3)
  -- We use induction to show the sum is always ≡ 0 (mod 3)
  have h_base : (∑ k ∈ Finset.Icc 3 (6 - 2), (6 + k - 2) : ℕ) = 15 := by decide
  have h_ind : ∀ m ≥ 6, (∑ k ∈ Finset.Icc 3 (m + 1 - 2), (m + 1 + k - 2) : ℕ) =
                   (∑ k ∈ Finset.Icc 3 (m - 2), (m + k - 2) : ℕ) + 3 * (m - 2) := by
    intro m hm
    -- Icc 3 (m-1) = Icc 3 (m-2) ∪ {m-1} when m ≥ 6
    have hIcc : Finset.Icc 3 (m + 1 - 2) = Finset.Icc 3 (m - 2) ∪ {m - 1} := by
      ext x
      simp [Finset.mem_Icc]
      omega
    rw [hIcc, Finset.sum_union]
    · -- LHS: ∑ x in Icc 3 (m-2), (m + 1 + x - 2) + (m + 1 + (m-1) - 2)
      --     = ∑ x in Icc 3 (m-2), (m + x - 1) + (2m - 2)
      -- RHS: ∑ k in Icc 3 (m-2), (m + k - 2) + 3(m - 2)
      -- Difference: ∑ x in Icc 3 (m-2), 1 + (2m - 2) - 3(m - 2) = (m-4) + 2m - 2 - 3m + 6 = 0
      simp [Finset.sum_singleton]
      have hcard : (Finset.Icc 3 (m - 2)).card = m - 4 := by simp [Nat.card_Icc]; omega
      rw [show (fun x => m + 1 + x - 2) = (fun x => m + x - 2 + 1) by ext x; omega]
      rw [Finset.sum_add_distrib]
      simp [hcard]
      omega
    · simp [Finset.disjoint_singleton_right]
      omega
  -- Now use induction to show S(n) ≡ 0 (mod 3) for all n ≥ 6
  -- We show that 3 ∣ S(n)
  have h_div : 3 ∣ ∑ k ∈ Finset.Icc 3 (n - 2), (n + k - 2) := by
    -- Use strong induction on n
    -- Base: S(6) = 15, 3 ∣ 15
    -- Step: S(m+1) = S(m) + 3(m-2), so 3 ∣ S(m) implies 3 ∣ S(m+1)
    have h_shift : n = (n - 6) + 6 := by omega
    rw [h_shift]
    induction n - 6 with
    | zero =>
      -- n = 6
      simp [h_base]
    | succ m ih =>
      -- n = m + 7
      -- h_ind (m + 6) says: S(m+7) = S(m+6) + 3(m+4)
      have h_eq : ∑ k ∈ Finset.Icc 3 ((m + 6) + 1 - 2), ((m + 6) + 1 + k - 2) =
                  ∑ k ∈ Finset.Icc 3 (m + 6 - 2), (m + 6 + k - 2) + 3 * (m + 4) := by
        convert h_ind (m + 6) (by omega) using 2
      -- ih says 3 ∣ S(m + 6)
      have hi' : 3 ∣ ∑ k ∈ Finset.Icc 3 (m + 6 - 2), (m + 6 + k - 2) := ih
      -- The goal is 3 ∣ S(m + 7) = S(m + 6) + 3(m + 4)
      convert h_eq ▸ Nat.dvd_add hi' (dvd_mul_right 3 (m + 4)) using 1
  obtain ⟨k, hk⟩ := h_div
  rw [hk, Nat.cast_mul]
  simp only [Nat.cast_ofNat, mul_eq_zero]
  left
  exact ZMod.natCast_self 3

/-- Reindex the sum of window contributions by trichord class, using one
chosen realizing position for each class. -/
lemma contribution_sum_by_class (hn : 6 ≤ n) [NeZero (n - 3)]
    (D : ZMod (n - 3) → ZMod n) (P : ℕ → ZMod (n - 3))
    (hP : ∀ k ∈ Finset.Icc 2 (n - 2),
      RealizesClass n k (D (P k)) (D (P k + 1))) :
    (∑ i : ZMod (n - 3), (w n (D (i + 1)) - w n (D i))) =
      ∑ k ∈ Finset.Icc 2 (n - 2), (w n (D (P k + 1)) - w n (D (P k))) := by
  let S := Finset.Icc 2 (n - 2)
  have hPinj : Set.InjOn P (↑S : Set ℕ) := by
    intro k hk k' hk' heq
    apply realizes_class_unique n hn (by simpa [S] using hk)
      (by simpa [S] using hk') (hP k (by simpa [S] using hk))
    simpa [heq] using hP k' (by simpa [S] using hk')
  have hcardS : S.card = n - 3 := by
    simp [S, Nat.card_Icc]
    omega
  have hcardZ : Fintype.card (ZMod (n - 3)) = n - 3 := ZMod.card (n - 3)
  symm
  apply Finset.sum_bij (fun k _ => P k)
  · intro k hk
    exact Finset.mem_univ _
  · intro k hk k' hk' heq
    exact hPinj (by simpa [S] using hk) (by simpa [S] using hk') heq
  · intro i hi
    have hle : (Finset.univ : Finset (ZMod (n - 3))).card ≤ S.card := by
      rw [Finset.card_univ, hcardZ, hcardS]
    have hsurj : Set.SurjOn P (↑S : Set ℕ) (↑(Finset.univ : Finset (ZMod (n - 3)))) :=
      Finset.surjOn_of_injOn_of_card_le P (by intro x hx; simp) hPinj hle
    obtain ⟨k, hk, heq⟩ := hsurj (by simp)
    exact ⟨k, by simpa [S] using hk, heq⟩
  · intro k hk
    rfl

/-- The class-indexed contribution sum of a zigzag chromatic window is
`±n` modulo three; all nonchromatic class fees cancel. -/
lemma class_contribution_sum_zigzag (hn : 6 ≤ n)
    (D : ZMod (n - 3) → ZMod n) (P : ℕ → ZMod (n - 3))
    (hP : ∀ k ∈ Finset.Icc 2 (n - 2),
      RealizesClass n k (D (P k)) (D (P k + 1)))
    (hzP : ¬ (D (P 2 + 1) = D (P 2) ∧ (D (P 2) = 1 ∨ D (P 2) = -1))) :
    (∑ k ∈ Finset.Icc 2 (n - 2), (w n (D (P k + 1)) - w n (D (P k)))) =
      (n : ZMod 3) ∨
    (∑ k ∈ Finset.Icc 2 (n - 2), (w n (D (P k + 1)) - w n (D (P k)))) =
      -(n : ZMod 3) := by
  have h2mem : 2 ∈ Finset.Icc 2 (n - 2) := by simp; omega
  have hsplit : Finset.Icc 2 (n - 2) = insert 2 (Finset.Icc 3 (n - 2)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h2not : 2 ∉ Finset.Icc 3 (n - 2) := by simp
  have hnonchrom :
      (∑ k ∈ Finset.Icc 3 (n - 2), (w n (D (P k + 1)) - w n (D (P k)))) = 0 := by
    calc
      _ = ∑ k ∈ Finset.Icc 3 (n - 2), ((n + k - 2 : ℕ) : ZMod 3) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply form_contribution n hn k
        · simpa using hk
        · exact hP k (by simp only [Finset.mem_Icc] at hk ⊢; omega)
      _ = 0 := by
        simpa only [Nat.cast_sum] using fee_sum n hn
  have hchrom := chromatic_contribution n hn (D (P 2)) (D (P 2 + 1)) (hP 2 h2mem)
  rw [hsplit, Finset.sum_insert h2not]
  rw [hnonchrom, add_zero]
  rcases hchrom with hs | hz
  · exact False.elim (hzP ⟨hs.1, hs.2.1⟩)
  · exact hz.2

/-- **Main theorem.**  Any interval cycle of any drift
presenting the chromatic in zigzag forces 3 ∣ n.
Proof outline: (i) `choose K hKmem hK using fun i => exists_class_at n hn D hD i`
gives the class function; with `realizes_class_unique` and the `∃!` of
`hD`, `K` is a bijection onto `Finset.Icc 2 (n-2)`.
(ii) Reindex `telescope`:
  0 = ∑ i, (w n (D (i+1)) - w n (D i))
    = ∑ k ∈ Icc 2 (n-2), (contribution of the window of class k)
via `Finset.sum_bij` (map i ↦ K i).
(iii) Split off k = 2 (`Finset.sum_eq_sum_diff_singleton_add` or
`Finset.add_sum_erase`), evaluate the k ≥ 3 part by
`form_contribution` and `fee_sum` (note
`∑ k ∈ Icc 3 (n-2), ((n+k-2 : ℕ) : ZMod 3)
  = ((∑ k ∈ Icc 3 (n-2), (n+k-2) : ℕ) : ZMod 3)` by `Nat.cast_sum`),
leaving 0 = χ where χ is the chromatic window's contribution.
(iv) `hz` gives a position with `ChromaticAt` and the non-scalar shape;
by uniqueness it is the class-2 position, so `chromatic_contribution`
puts χ ∈ {(n : ZMod 3), -(n : ZMod 3)} (the scalar branch is excluded
by the non-scalar shape).  Hence (n : ZMod 3) = 0, i.e.
`(ZMod.natCast_zmod_eq_zero_iff_dvd n 3).mp`, giving 3 ∣ n. -/
theorem zigzag_three_dvd (hn : 6 ≤ n) (D : ZMod (n - 3) → ZMod n)
    (hD : IsIntervalCycle n D) (hz : IsZigzag n D) : 3 ∣ n := by
  classical
  letI : NeZero (n - 3) := ⟨by omega⟩
  let P : ℕ → ZMod (n - 3) := fun k =>
    if hk : k ∈ Finset.Icc 2 (n - 2) then Classical.choose (hD k hk) else 0
  have hP : ∀ k ∈ Finset.Icc 2 (n - 2),
      RealizesClass n k (D (P k)) (D (P k + 1)) := by
    intro k hk
    simp only [P, dif_pos hk]
    exact (Classical.choose_spec (hD k hk)).1
  obtain ⟨j, hjchrom, hjshape⟩ := hz
  have h2mem : 2 ∈ Finset.Icc 2 (n - 2) := by simp; omega
  have hPj : P 2 = j := by
    exact (hD 2 h2mem).unique (hP 2 h2mem) hjchrom
  have hzP : ¬ (D (P 2 + 1) = D (P 2) ∧
      (D (P 2) = 1 ∨ D (P 2) = -1)) := by
    simpa [hPj] using hjshape
  have hreindex := contribution_sum_by_class n hn D P hP
  have heval := class_contribution_sum_zigzag n hn D P hP hzP
  have ht := telescope n hn D
  unfold cyclicSum at ht
  simp only [dif_neg (by omega : n - 3 ≠ 0)] at ht
  rw [hreindex] at ht
  have hnzero : (n : ZMod 3) = 0 := by
    rcases heval with heval | heval
    · rw [heval] at ht
      exact ht
    · rw [heval] at ht
      simpa using congrArg Neg.neg ht
  have hv := congrArg ZMod.val hnzero
  rw [ZMod.val_natCast] at hv
  simp at hv
  exact Nat.dvd_of_mod_eq_zero hv

/-- Corollary for pitch cycles (paper Theorem 6.1 as stated). -/
theorem cycle_zigzag_three_dvd (hn : 6 ≤ n) (c : ZMod (n - 3) → ZMod n)
    (hc : IsCycle n c) (hz : IsZigzag n (stepsOf n c)) : 3 ∣ n :=
  zigzag_three_dvd n hn _ hc hz
end

/- ==================== §3 THE EXCEPTIONAL TEMPERAMENTS 6 AND 12 ==================== -/

section
/-
  Phase 1: the exceptional temperaments (paper Prop. 7.1 / Thm 8.3 parts).

  n = 6:  NO cycles exist at all — small enough for kernel `decide`
          over all 6^3 = 216 pitch words (or state via step words).
  n = 12: no closed (drift-0) zigzag interval cycle exists.  Direct
          enumeration of step words is ~12^9 and too large; instead use
          the CERTIFICATE ROUTE: from a zigzag drift-0 cycle derive a
          "plan" F : Fin 9 → Fin 6 (a form choice per class) with
            (i)  multiset of first entries = multiset of second entries
                 (both equal the step multiset, via the position↔class
                 bijection),
            (ii) sum of first entries = 0 in ZMod 12,
            (iii) the class-2 form is zigzag (index ∈ {1,2,3,4}),
          then kill all 6^9 = 10,077,696 candidates by `native_decide`.
-/


/-- The six form pairs of class `k` in `ZMod n` (index order I..VI). -/
def formPair (n k : ℕ) : Fin 6 → ZMod n × ZMod n :=
  ![((1 : ZMod n), (k : ZMod n) - 1),
    ((k : ZMod n), 1 - (k : ZMod n)),
    (-1, (k : ZMod n)),
    ((k : ZMod n) - 1, -(k : ZMod n)),
    (-(k : ZMod n), (1 : ZMod n)),
    (1 - (k : ZMod n), -1)]

/-- A balanced, closed, zigzag plan at n = 12 (classes k = idx + 2). -/
def BadPlan12 (F : Fin 9 → Fin 6) : Prop :=
  (Multiset.map (fun i => (formPair 12 (i.val + 2) (F i)).1) Finset.univ.val
    = Multiset.map (fun i => (formPair 12 (i.val + 2) (F i)).2) Finset.univ.val)
  ∧ (∑ i : Fin 9, (formPair 12 (i.val + 2) (F i)).1) = 0
  ∧ (F 0 = 1 ∨ F 0 = 2 ∨ F 0 = 3 ∨ F 0 = 4)

/-- Bool-valued checker for `BadPlan12` . -/
def badPlanCheck (F : Fin 9 → Fin 6) : Bool :=
  (decide (F 0 = 1) || decide (F 0 = 2) || decide (F 0 = 3) || decide (F 0 = 4))
    && decide ((∑ i : Fin 9, (formPair 12 (i.val + 2) (F i)).1) = 0)
    && ((List.finRange 12).all (fun v =>
        ((List.finRange 9).countP
            (fun i => decide ((formPair 12 (i.val + 2) (F i)).1 = ((v.val : ℕ) : ZMod 12))))
          == ((List.finRange 9).countP
            (fun i => decide ((formPair 12 (i.val + 2) (F i)).2 = ((v.val : ℕ) : ZMod 12))))))

set_option maxHeartbeats 400000 in
set_option maxRecDepth 10000 in
/-- Equality of the first/second form-entry multisets is equivalent to the
finite count test used by `badPlanCheck`. -/
lemma form_multiset_eq_iff_counts (F : Fin 9 → Fin 6) :
    (Multiset.map (fun i => (formPair 12 (i.val + 2) (F i)).1) Finset.univ.val
      = Multiset.map (fun i => (formPair 12 (i.val + 2) (F i)).2) Finset.univ.val) ↔
    (List.finRange 12).all (fun v =>
      ((List.finRange 9).countP
          (fun i => decide ((formPair 12 (i.val + 2) (F i)).1 = ((v.val : ℕ) : ZMod 12))))
        == ((List.finRange 9).countP
          (fun i => decide ((formPair 12 (i.val + 2) (F i)).2 = ((v.val : ℕ) : ZMod 12))))) = true := by
  constructor
  · intro h
    rw [List.all_eq_true]
    intro v hv
    have hc := Multiset.ext.1 h ((v.val : ℕ) : ZMod 12)
    apply (beq_iff_eq).2
    simpa only [Fin.univ_def, Multiset.count_map, Multiset.filter_coe,
      List.countP_eq_length_filter, Multiset.coe_card,
      decide_eq_true_eq, eq_comm] using hc
  · intro h
    apply Multiset.ext.2
    intro x
    rw [List.all_eq_true] at h
    let v : Fin 12 := ⟨x.val, x.val_lt⟩
    have hv := h v (List.mem_finRange v)
    have hx : ((v.val : ℕ) : ZMod 12) = x := ZMod.natCast_zmod_val x
    rw [hx] at hv
    have hv' := (beq_iff_eq).1 hv
    simpa only [Fin.univ_def, Multiset.count_map, Multiset.filter_coe,
      List.countP_eq_length_filter, Multiset.coe_card,
      decide_eq_true_eq, eq_comm] using hv'

/-- Reflection: the checker decides `BadPlan12`.
Proof outline: the multiset equality is equivalent to equality of counts at every
element of `ZMod 12` (`Multiset.ext`); `Multiset.count_map` turns each
count into a `countP` over `Finset.univ.val`, and
`Finset.univ.val = ↑(List.finRange 9)` for `Fin 9`
(`Fin.univ_def`/`List.finRange` simp lemmas); every element of
`ZMod 12` is `((v.val : ℕ) : ZMod 12)` for a unique `v : Fin 12`
(`ZMod.natCast_val`-style, or use that `ZMod 12` is `Fin 12`).  The sum
and disjunction conjuncts are direct `decide`/`Bool` bridges
(`Bool.and_eq_true`, `decide_eq_true_iff`, `beq_iff_eq`). -/
theorem badPlan_iff (F : Fin 9 → Fin 6) :
    BadPlan12 F ↔ badPlanCheck F = true := by
  unfold BadPlan12 badPlanCheck
  rw [form_multiset_eq_iff_counts F]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  tauto

/-- Any `F : Fin 9 → Fin 6` equals the tabulation of its nine values. -/
theorem tabulate_eq (F : Fin 9 → Fin 6) :
    F = ![F 0, F 1, F 2, F 3, F 4, F 5, F 6, F 7, F 8] := by
  funext i
  fin_cases i <;> rfl

set_option maxHeartbeats 400000 in
/-- Certificate slice: no bad plan whose class-2 form index is 0. -/
theorem no_bad_head_0 : ∀ d1 d2 d3 d4 d5 d6 d7 d8 : Fin 6,
    badPlanCheck ![0, d1, d2, d3, d4, d5, d6, d7, d8] = false := by
  native_decide

set_option maxHeartbeats 400000 in
/-- Certificate slice: no bad plan whose class-2 form index is 1. -/
theorem no_bad_head_1 : ∀ d1 d2 d3 d4 d5 d6 d7 d8 : Fin 6,
    badPlanCheck ![1, d1, d2, d3, d4, d5, d6, d7, d8] = false := by
  native_decide

set_option maxHeartbeats 400000 in
/-- Certificate slice: no bad plan whose class-2 form index is 2. -/
theorem no_bad_head_2 : ∀ d1 d2 d3 d4 d5 d6 d7 d8 : Fin 6,
    badPlanCheck ![2, d1, d2, d3, d4, d5, d6, d7, d8] = false := by
  native_decide

set_option maxHeartbeats 400000 in
/-- Certificate slice: no bad plan whose class-2 form index is 3. -/
theorem no_bad_head_3 : ∀ d1 d2 d3 d4 d5 d6 d7 d8 : Fin 6,
    badPlanCheck ![3, d1, d2, d3, d4, d5, d6, d7, d8] = false := by
  native_decide

set_option maxHeartbeats 400000 in
/-- Certificate slice: no bad plan whose class-2 form index is 4. -/
theorem no_bad_head_4 : ∀ d1 d2 d3 d4 d5 d6 d7 d8 : Fin 6,
    badPlanCheck ![4, d1, d2, d3, d4, d5, d6, d7, d8] = false := by
  native_decide

set_option maxHeartbeats 400000 in
/-- Certificate slice: no bad plan whose class-2 form index is 5. -/
theorem no_bad_head_5 : ∀ d1 d2 d3 d4 d5 d6 d7 d8 : Fin 6,
    badPlanCheck ![5, d1, d2, d3, d4, d5, d6, d7, d8] = false := by
  native_decide

/--.  The finite certificate.
The enumeration is split into six slices `no_bad_head_0 … no_bad_head_5`
according to the value of `F 0`, each of which quantifies over eight
nested copies of `Fin 6`.  This avoids building `Finset.univ` for the
function space `Fin 9 → Fin 6`, and keeps every slice inside the
standard elaboration budget. -/
theorem no_bad_plan_12 : ¬ ∃ F : Fin 9 → Fin 6, BadPlan12 F := by
  rintro ⟨F, hF⟩
  have hchk : badPlanCheck F = true := (badPlan_iff F).mp hF
  have h2 : badPlanCheck ![F 0, F 1, F 2, F 3, F 4, F 5, F 6, F 7, F 8]
      = true := by rw [← tabulate_eq F]; exact hchk
  have hcases : ∀ x : Fin 6, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
    decide
  rcases hcases (F 0) with h0 | h0 | h0 | h0 | h0 | h0 <;> rw [h0] at h2
  · rw [no_bad_head_0 (F 1) (F 2) (F 3) (F 4) (F 5) (F 6) (F 7) (F 8)] at h2
    exact Bool.false_ne_true h2
  · rw [no_bad_head_1 (F 1) (F 2) (F 3) (F 4) (F 5) (F 6) (F 7) (F 8)] at h2
    exact Bool.false_ne_true h2
  · rw [no_bad_head_2 (F 1) (F 2) (F 3) (F 4) (F 5) (F 6) (F 7) (F 8)] at h2
    exact Bool.false_ne_true h2
  · rw [no_bad_head_3 (F 1) (F 2) (F 3) (F 4) (F 5) (F 6) (F 7) (F 8)] at h2
    exact Bool.false_ne_true h2
  · rw [no_bad_head_4 (F 1) (F 2) (F 3) (F 4) (F 5) (F 6) (F 7) (F 8)] at h2
    exact Bool.false_ne_true h2
  · rw [no_bad_head_5 (F 1) (F 2) (F 3) (F 4) (F 5) (F 6) (F 7) (F 8)] at h2
    exact Bool.false_ne_true h2

/-- Reindexing a multiset over `Finset.univ` along an equivalence. -/
lemma multiset_map_univ_equiv {α β γ : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → γ) :
    Multiset.map (fun a => f (e a)) (Finset.univ : Finset α).val
      = Multiset.map f (Finset.univ : Finset β).val := by
  conv_rhs => rw [← Finset.map_univ_equiv e]
  rw [Finset.map_val, Multiset.map_map]
  rfl

/-- Reindexing a multiset over `ZMod m` along the shift by one. -/
lemma multiset_map_univ_shift {m : ℕ} [NeZero m] {γ : Type*} (f : ZMod m → γ) :
    Multiset.map (fun j => f (j + 1)) (Finset.univ : Finset (ZMod m)).val
      = Multiset.map f (Finset.univ : Finset (ZMod m)).val := by
  simpa using multiset_map_univ_equiv (Equiv.addRight (1 : ZMod m)) f

/-- Every realizing pair is one of the six form pairs; this records the index. -/
lemma exists_form_index (n : ℕ) (hn : 6 ≤ n) (k : ℕ) (hk : 2 ≤ k ∧ k ≤ n - 2)
    (a b : ZMod n) (h : RealizesClass n k a b) :
    ∃ f : Fin 6, formPair n k f = (a, b) := by
  rcases (realizes_iff_form n hn k hk a b).mp h with h' | h' | h' | h' | h' | h'
  · exact ⟨0, by simp [formPair, h']⟩
  · exact ⟨1, by simp [formPair, h']⟩
  · exact ⟨2, by simp [formPair, h']⟩
  · exact ⟨3, by simp [formPair, h']⟩
  · exact ⟨4, by simp [formPair, h']⟩
  · exact ⟨5, by simp [formPair, h']⟩

/-- Cycle-to-plan: a zigzag pitch cycle at n = 12 yields a
bad plan.  Proof outline: specialize the the corresponding step infrastructure to n = 12: for
class k = i.val + 2 take its unique position `p i` from `hD`, and let
`F i` be the form index given by `realizes_iff_form` (choice over the
six-fold disjunction).  Multiset condition: the map i ↦ p i is a
bijection `Fin 9 ≃ ZMod 9` (uniqueness + `exists_class_at`), under
which the multiset of first entries is the multiset of steps
`(stepsOf 12 c)` and the multiset of second entries is its shift by
`Equiv.addRight 1` — hence they are equal.  Sum condition:
`drift_stepsOf`.  Chromatic condition: `hz` locates the class-2 window;
its form index is ∈ {1,2,3,4} because indices 0 and 5 are exactly the
scalar shapes. -/
theorem cycle_gives_bad_plan (c : ZMod 9 → ZMod 12)
    (hc : IsCycle 12 c) (hz : IsZigzag 12 (stepsOf 12 c)) :
    ∃ F : Fin 9 → Fin 6, BadPlan12 F := by
  classical
  set D : ZMod 9 → ZMod 12 := stepsOf 12 c with hDdef
  have hD : IsIntervalCycle 12 D := hc
  have hmem : ∀ i : Fin 9, (i.val + 2) ∈ Finset.Icc 2 (12 - 2) := by
    intro i
    have := i.isLt
    simp only [Finset.mem_Icc]
    omega
  -- chosen position for each class
  let P : ℕ → ZMod 9 := fun k =>
    if hk : k ∈ Finset.Icc 2 (12 - 2) then Classical.choose (hD k hk) else 0
  have hP : ∀ k, ∀ hk : k ∈ Finset.Icc 2 (12 - 2),
      RealizesClass 12 k (D (P k)) (D (P k + 1)) := by
    intro k hk
    simp only [P, dif_pos hk]
    exact (Classical.choose_spec (hD k hk)).1
  let q : Fin 9 → ZMod 9 := fun i => P (i.val + 2)
  have hqreal : ∀ i : Fin 9,
      RealizesClass 12 (i.val + 2) (D (q i)) (D (q i + 1)) :=
    fun i => hP _ (hmem i)
  have hqinj : Function.Injective q := by
    intro i j hij
    have h1 := hqreal i
    have h2 : RealizesClass 12 (j.val + 2) (D (q i)) (D (q i + 1)) := by
      rw [hij]; exact hqreal j
    have hi := i.isLt
    have hj := j.isLt
    have := realizes_class_unique 12 (by norm_num)
      (by omega : 2 ≤ i.val + 2 ∧ i.val + 2 ≤ 12 - 2)
      (by omega : 2 ≤ j.val + 2 ∧ j.val + 2 ≤ 12 - 2) h1 h2
    exact Fin.ext (by omega)
  have hqbij : Function.Bijective q :=
    (Fintype.bijective_iff_injective_and_card q).2 ⟨hqinj, by simp⟩
  let e : Fin 9 ≃ ZMod 9 := Equiv.ofBijective q hqbij
  have he : ∀ i, e i = q i := fun i => rfl
  -- choose a form index for each class
  have hform : ∀ i : Fin 9, ∃ f : Fin 6,
      formPair 12 (i.val + 2) f = (D (q i), D (q i + 1)) := by
    intro i
    have hi := i.isLt
    exact exists_form_index 12 (by norm_num) (i.val + 2)
      (by omega) _ _ (hqreal i)
  choose F hF using hform
  have hF1 : ∀ i : Fin 9, (formPair 12 (i.val + 2) (F i)).1 = D (q i) := by
    intro i; rw [hF i]
  have hF2 : ∀ i : Fin 9, (formPair 12 (i.val + 2) (F i)).2 = D (q i + 1) := by
    intro i; rw [hF i]
  refine ⟨F, ?_, ?_, ?_⟩
  · -- balance
    have h1 : Multiset.map (fun i : Fin 9 => (formPair 12 (i.val + 2) (F i)).1)
        (Finset.univ : Finset (Fin 9)).val
        = Multiset.map (fun i : Fin 9 => D (e i)) (Finset.univ : Finset (Fin 9)).val := by
      apply Multiset.map_congr rfl
      intro i _
      rw [hF1 i, he i]
    have h2 : Multiset.map (fun i : Fin 9 => (formPair 12 (i.val + 2) (F i)).2)
        (Finset.univ : Finset (Fin 9)).val
        = Multiset.map (fun i : Fin 9 => (fun j : ZMod 9 => D (j + 1)) (e i))
          (Finset.univ : Finset (Fin 9)).val := by
      apply Multiset.map_congr rfl
      intro i _
      rw [hF2 i, he i]
    rw [h1, h2, multiset_map_univ_equiv e D,
      multiset_map_univ_equiv e (fun j : ZMod 9 => D (j + 1)),
      multiset_map_univ_shift D]
  · -- drift zero
    have h1 : (∑ i : Fin 9, (formPair 12 (i.val + 2) (F i)).1)
        = ∑ i : Fin 9, D (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hF1 i, he i]
    have h2 : (∑ i : Fin 9, D (e i)) = ∑ j : ZMod 9, D j := Equiv.sum_comp e D
    have h3 : drift 12 D = 0 := drift_stepsOf 12 (by norm_num) c
    rw [h1, h2]
    have h4 : drift 12 D = ∑ j : ZMod 9, D j := by
      unfold drift cyclicSum
      simp
    rw [← h4]
    exact h3
  · -- chromatic form index
    obtain ⟨j, hjchrom, hjshape⟩ := hz
    have h2mem : (2 : ℕ) ∈ Finset.Icc 2 (12 - 2) := by simp
    have hPj : P 2 = j := (hD 2 h2mem).unique (hP 2 h2mem) hjchrom
    have hq0 : q 0 = j := by
      show P ((0 : Fin 9).val + 2) = j
      simpa using hPj
    have hFj : formPair 12 2 (F 0) = (D j, D (j + 1)) := by
      have := hF 0
      simpa [hq0] using this
    have hne0 : F 0 ≠ 0 := by
      intro h
      rw [h] at hFj
      have h1 : D j = 1 := by
        have := congrArg Prod.fst hFj
        simpa [formPair] using this.symm
      have h2 : D (j + 1) = 1 := by
        have := congrArg Prod.snd hFj
        simp [formPair] at this
        rw [← this]
        decide +kernel
      exact hjshape ⟨by rw [h1, h2], Or.inl h1⟩
    have hne5 : F 0 ≠ 5 := by
      intro h
      rw [h] at hFj
      have h1 : D j = -1 := by
        have := congrArg Prod.fst hFj
        simp [formPair] at this
        rw [← this]
        decide +kernel
      have h2 : D (j + 1) = -1 := by
        have := congrArg Prod.snd hFj
        simpa [formPair] using this.symm
      exact hjshape ⟨by rw [h1, h2], Or.inr h1⟩
    have hcases : ∀ x : Fin 6, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
      decide
    rcases hcases (F 0) with h | h | h | h | h | h <;> tauto

/-- The Missing Zigzag Theorem for twelve-tone equal temperament. -/
theorem twelve_no_zigzag (c : ZMod 9 → ZMod 12) (hc : IsCycle 12 c) :
    ¬ IsZigzag 12 (stepsOf 12 c) :=
  fun hz => no_bad_plan_12 (cycle_gives_bad_plan c hc hz)

set_option maxRecDepth 4000 in
/-- n = 6 admits no cycles whatsoever (216 candidates;
kernel `decide` should suffice, `native_decide` certainly). -/
theorem six_no_cycle (c : ZMod 3 → ZMod 6) : ¬ IsCycle 6 c := by
  revert c
  unfold IsCycle IsIntervalCycle
  simp only [ExistsUnique]
  decide
end

/- ==================== §4 EXISTENCE AND CLASSIFICATION ==================== -/

section
/-
  Phase 1 tail + Phase 2 head: existence.

  Explicit witnesses at n = 9, 15, 18, 21 are concrete finite checks
  (`decide` should work; `native_decide` as fallback — RealizesClass
  quantifies ∃ t over ZMod n with a Finset equality, all decidable).
  The full classification is proved below.

  Witness data (verified computationally, paper Examples 2.5/2.6 and
  Lemma 8.1 bases):
    n =  9 : (0, 1, 4, 3, 8, 2)
    n = 15 : (0, 2, 1, 6, 0, 14, 9, 13, 10, 11, 4, 3)
    n = 18 : (0, 2, 1, 4, 0, 17, 8, 16, 15, 9, 10, 5, 11, 4, 3)
    n = 21 : (0, 2, 1, 4, 5, 12, 6, 11, 10, 16, 17, 9, 18, 8, 7, 19, 20, 3)
-/


/-- Explicit zigzag witness in 9TET: the cycle `(0,1,4,3,8,2)`. -/
theorem exists_zigzag_nine :
    ∃ c : ZMod 6 → ZMod 9, IsCycle 9 c ∧ IsZigzag 9 (stepsOf 9 c) := by
  refine ⟨(fun i => ![0, 1, 4, 3, 8, 2] ⟨i.val, i.val_lt⟩), ?_⟩
  unfold IsCycle IsIntervalCycle IsZigzag ChromaticAt
  simp only [ExistsUnique]
  decide

/-- (same pattern; witness above). -/
theorem exists_zigzag_fifteen :
    ∃ c : ZMod 12 → ZMod 15, IsCycle 15 c ∧ IsZigzag 15 (stepsOf 15 c) := by
  refine ⟨(fun i => ![0, 2, 1, 6, 0, 14, 9, 13, 10, 11, 4, 3]
    ⟨i.val, i.val_lt⟩), ?_⟩
  unfold IsCycle IsIntervalCycle IsZigzag ChromaticAt
  simp only [ExistsUnique]
  decide

/-- (n = 18 and n = 21 alike; witnesses above). -/
theorem exists_zigzag_eighteen :
    ∃ c : ZMod 15 → ZMod 18, IsCycle 18 c ∧ IsZigzag 18 (stepsOf 18 c) := by
  refine ⟨(fun i => ![0, 2, 1, 4, 0, 17, 8, 16, 15, 9, 10, 5, 11, 4, 3]
    ⟨i.val, i.val_lt⟩), ?_⟩
  unfold IsCycle IsIntervalCycle IsZigzag ChromaticAt
  simp only [ExistsUnique]
  decide

/- ==================== §7 PHASE 2: THE PUMPING CONSTRUCTION ==================== -/

section Phase2
/-
  Existence, by the closed-form word route.  No graph theory: for each residue class of `n` mod 6 an
  explicit `ℤ`-valued step word and an explicit class assignment are
  written down, and `IsIntervalCycle` is verified directly.
-/

/-- Close an identity in `ZMod n` that is either a ring identity or follows
from the modulus relation `h : (n : ZMod n) = 0` with coefficient `±1`. -/
local macro "modclose " h:term : tactic =>
  `(tactic| first | ring1 | linear_combination ($h) | linear_combination (-($h)))

/-! ### Stage 1a — the six forms realize their class

Each of the six form pairs of Appendix A realizes its class outright; unlike
`realizes_iff_form` these need no bound on `k` at all, because they only
exhibit the translate. -/

lemma realizes_I (n k : ℕ) (a b : ZMod n) (ha : a = 1) (hb : b = (k : ZMod n) - 1) :
    RealizesClass n k a b := by
  subst ha; subst hb; exact ⟨0, by norm_num⟩

lemma realizes_II (n k : ℕ) (a b : ZMod n) (ha : a = (k : ZMod n))
    (hb : b = 1 - (k : ZMod n)) : RealizesClass n k a b := by
  subst ha; subst hb
  refine ⟨0, ?_⟩
  rw [show (k : ZMod n) + (1 - (k : ZMod n)) = 1 by ring]
  ext x; simp; tauto

lemma realizes_III (n k : ℕ) (a b : ZMod n) (ha : a = -1) (hb : b = (k : ZMod n)) :
    RealizesClass n k a b := by
  subst ha; subst hb
  refine ⟨-1, ?_⟩
  rw [show (-1 : ZMod n) + 1 = 0 by ring]
  ext x; simp; tauto

lemma realizes_IV (n k : ℕ) (a b : ZMod n) (ha : a = (k : ZMod n) - 1)
    (hb : b = -(k : ZMod n)) : RealizesClass n k a b := by
  subst ha; subst hb
  refine ⟨-1, ?_⟩
  rw [show (-1 : ZMod n) + 1 = 0 by ring,
    show (k : ZMod n) - 1 + -(k : ZMod n) = -1 by ring]
  ext x; simp [sub_eq_add_neg, add_comm]; tauto

lemma realizes_V (n k : ℕ) (a b : ZMod n) (ha : a = -(k : ZMod n)) (hb : b = 1) :
    RealizesClass n k a b := by
  subst ha; subst hb
  refine ⟨-(k : ZMod n), ?_⟩
  rw [show -(k : ZMod n) + (k : ZMod n) = 0 by ring]
  ext x; simp; tauto

lemma realizes_VI (n k : ℕ) (a b : ZMod n) (ha : a = 1 - (k : ZMod n)) (hb : b = -1) :
    RealizesClass n k a b := by
  subst ha; subst hb
  refine ⟨-(k : ZMod n), ?_⟩
  rw [show -(k : ZMod n) + (k : ZMod n) = 0 by ring,
    show (1 : ZMod n) - (k : ZMod n) + -1 = -(k : ZMod n) by ring]
  ext x; simp [sub_eq_add_neg, add_comm]; tauto

/-! ### Stage 1b — from a class assignment to an interval cycle -/

/-- If every window of `D` realizes the class `K i`, and `K` is an injective
map into the class range, then `D` is an interval cycle: injectivity plus the
cardinality `#(Icc 2 (n-2)) = n - 3` makes `K` a bijection, and uniqueness is
`realizes_class_unique`. -/
theorem isIntervalCycle_of_classMap (n : ℕ) (hn : 6 ≤ n)
    (D : ZMod (n - 3) → ZMod n) (K : ZMod (n - 3) → ℕ)
    (hKmem : ∀ i, K i ∈ Finset.Icc 2 (n - 2)) (hKinj : Function.Injective K)
    (hreal : ∀ i, RealizesClass n (K i) (D i) (D (i + 1))) :
    IsIntervalCycle n D := by
  classical
  haveI : NeZero (n - 3) := ⟨by omega⟩
  have hsurj : ∀ k ∈ Finset.Icc 2 (n - 2), ∃ i, K i = k := by
    intro k hk
    have himg : (Finset.univ.image K) = Finset.Icc 2 (n - 2) := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_image] at hx
        obtain ⟨i, _, rfl⟩ := hx
        exact hKmem i
      · rw [Finset.card_image_of_injective _ hKinj, Finset.card_univ, ZMod.card,
          Nat.card_Icc]
        omega
    rw [← himg] at hk
    simpa using hk
  intro k hk
  obtain ⟨i, hi⟩ := hsurj k hk
  refine ⟨i, hi ▸ hreal i, ?_⟩
  intro j hj
  exact hKinj
    ((realizes_class_unique n hn (Finset.mem_Icc.mp (hKmem j)) (Finset.mem_Icc.mp hk)
      (hreal j) hj).trans hi.symm)

/-- Differencing the partial sums of an integer word recovers the word,
provided the word closes up modulo `n`. -/
theorem stepsOf_partialSum (n : ℕ) (hn : 6 ≤ n) (W : ℕ → ℤ)
    (hsum : ((∑ j ∈ Finset.range (n - 3), W j : ℤ) : ZMod n) = 0) (i : ZMod (n - 3)) :
    stepsOf n (fun j : ZMod (n - 3) => ((∑ l ∈ Finset.range j.val, W l : ℤ) : ZMod n)) i
      = ((W i.val : ℤ) : ZMod n) := by
  haveI : NeZero (n - 3) := ⟨by omega⟩
  haveI : Fact (1 < n - 3) := ⟨by omega⟩
  have hlt : i.val < n - 3 := ZMod.val_lt i
  simp only [stepsOf]
  rcases lt_or_ge (i.val + 1) (n - 3) with h | h
  · have h1 : ZMod.val (1 : ZMod (n - 3)) = 1 := ZMod.val_one _
    have hv : (i + 1).val = i.val + 1 := by
      rw [ZMod.val_add_of_lt (by rw [h1]; omega), h1]
    rw [hv, Finset.sum_range_succ]
    push_cast
    ring
  · have hival : i.val = n - 4 := by omega
    have hi1 : i + 1 = 0 := by
      have h2 : i = ((n - 4 : ℕ) : ZMod (n - 3)) := by
        rw [← hival]; simp [ZMod.natCast_val, ZMod.cast_id]
      rw [h2, show ((n - 4 : ℕ) : ZMod (n - 3)) + 1 = ((n - 3 : ℕ) : ZMod (n - 3)) by
        rw [show (n - 3 : ℕ) = (n - 4) + 1 by omega]; push_cast; ring, ZMod.natCast_self]
    rw [hi1]
    simp only [ZMod.val_zero, Finset.range_zero, Finset.sum_empty]
    rw [hival]
    rw [show (n - 3) = (n - 4) + 1 by omega, Finset.sum_range_succ] at hsum
    push_cast at hsum ⊢
    linear_combination -hsum

/-- **The word-to-cycle bridge.**  An integer step word `W` of length `n - 3`
that closes up mod `n`, together with an injective class assignment `K`
realized windowwise, produces a zigzag pitch cycle. -/
theorem exists_zigzag_of_word (n : ℕ) (hn : 9 ≤ n) (W : ℕ → ℤ) (K : ℕ → ℕ)
    (hsum : ((∑ j ∈ Finset.range (n - 3), W j : ℤ) : ZMod n) = 0)
    (hwrap : W (n - 3) = W 0)
    (hKmem : ∀ i < n - 3, 2 ≤ K i ∧ K i ≤ n - 2)
    (hKinj : ∀ i < n - 3, ∀ j < n - 3, K i = K j → i = j)
    (hreal : ∀ i < n - 3, RealizesClass n (K i) ((W i : ZMod n)) ((W (i + 1) : ZMod n)))
    (hK0 : K 0 = 2) (hW0 : ((W 0 : ℤ) : ZMod n) = 2) :
    ∃ c : ZMod (n - 3) → ZMod n, IsCycle n c ∧ IsZigzag n (stepsOf n c) := by
  haveI : NeZero (n - 3) := ⟨by omega⟩
  haveI : Fact (1 < n - 3) := ⟨by omega⟩
  set c : ZMod (n - 3) → ZMod n :=
    fun j : ZMod (n - 3) => ((∑ l ∈ Finset.range j.val, W l : ℤ) : ZMod n) with hc
  have hstep : ∀ i : ZMod (n - 3), stepsOf n c i = ((W i.val : ℤ) : ZMod n) :=
    stepsOf_partialSum n (by omega) W hsum
  have hvadd : ∀ i : ZMod (n - 3), W ((i + 1).val) = W (i.val + 1) := by
    intro i
    rw [ZMod.val_add, ZMod.val_one]
    rcases lt_or_ge (i.val + 1) (n - 3) with h | h
    · rw [Nat.mod_eq_of_lt h]
    · have : i.val + 1 = n - 3 := by have := ZMod.val_lt i; omega
      rw [this, Nat.mod_self, hwrap]
  have e0 : stepsOf n c 0 = 2 := by rw [hstep]; simpa using hW0
  refine ⟨c, ?_, ?_⟩
  · refine isIntervalCycle_of_classMap n (by omega) _ (fun i => K i.val)
      (fun i => Finset.mem_Icc.mpr (hKmem i.val (ZMod.val_lt i))) ?_ ?_
    · intro i j hij
      exact ZMod.val_injective _ (hKinj i.val (ZMod.val_lt i) j.val (ZMod.val_lt j) hij)
    · intro i
      rw [hstep, hstep, hvadd]
      exact hreal i.val (ZMod.val_lt i)
  · refine ⟨0, ?_, ?_⟩
    · show RealizesClass n 2 _ _
      rw [hstep, hstep, hvadd]
      simp only [ZMod.val_zero]
      rw [← hK0]
      exact hreal 0 (by omega)
    · rw [e0]
      rintro ⟨-, h | h⟩
      · have h1 := (ZMod.natCast_eq_natCast_iff' 2 1 n).mp (by push_cast; exact h)
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
        omega
      · have h2 : ((3 : ℕ) : ZMod n) = ((0 : ℕ) : ZMod n) := by
          push_cast; linear_combination h
        have h3 := (ZMod.natCast_eq_natCast_iff' 3 0 n).mp h2
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
        omega

/-! ### Stage 2A — the odd chain `n = 15 + 6t`

Word (signed): `[2, -1, 6]` then `t` blocks `[-L, -1, L+2, 1, -(L+1), L+2]` with
`L = 7 + 3s`, then the cap `-(7+3t)`, then the fixed suffix
`[-1, -3, 1, -5, 6, 1, 4, -3]`.  Its integer sum is `0`. -/

/-- The six entries of an odd-chain block with head level `L`. -/
def blkOdd (L : ℤ) : ℕ → ℤ
  | 0 => -L | 1 => -1 | 2 => L + 2 | 3 => 1 | 4 => -(L + 1) | _ => L + 2

/-- The eight-entry suffix of the odd-chain word; index `8` is the cyclic wrap
back to the first entry. -/
def sufOdd : ℕ → ℤ
  | 0 => -1 | 1 => -3 | 2 => 1 | 3 => -5 | 4 => 6 | 5 => 1 | 6 => 4 | 7 => -3 | _ => 2

/-- The odd-chain step word at `n = 15 + 6t`, as a function of the position. -/
def wOdd (t i : ℕ) : ℤ :=
  if i = 0 then 2 else if i = 1 then -1 else if i = 2 then 6
  else if i < 3 + 6 * t then blkOdd (7 + 3 * (((i - 3) / 6 : ℕ) : ℤ)) ((i - 3) % 6)
  else if i = 3 + 6 * t then -(7 + 3 * (t : ℤ))
  else sufOdd (i - (4 + 6 * t))

/-- The classes realized inside an odd-chain block. -/
def kBlkOdd (t s : ℕ) : ℕ → ℕ
  | 0 => 8 + 3 * s | 1 => 9 + 3 * s | 2 => 6 + 6 * t - 3 * s | 3 => 8 + 6 * t - 3 * s
  | 4 => 7 + 6 * t - 3 * s | _ => 10 + 3 * s

/-- The classes realized in the odd-chain suffix. -/
def kSufOdd (t : ℕ) : ℕ → ℕ
  | 0 => 12 + 6 * t | 1 => 3 | 2 => 11 + 6 * t | 3 => 10 + 6 * t | 4 => 9 + 6 * t
  | 5 => 5 | 6 => 4 | _ => 13 + 6 * t

/-- The class realized at position `i` of the odd-chain word. -/
def kOdd (t i : ℕ) : ℕ :=
  if i = 0 then 2 else if i = 1 then 6 else if i = 2 then 7
  else if i < 3 + 6 * t then kBlkOdd t ((i - 3) / 6) ((i - 3) % 6)
  else if i = 3 + 6 * t then 8 + 3 * t
  else kSufOdd t (i - (4 + 6 * t))

lemma wOdd_blk {t s r : ℕ} (hs : s < t) (hr : r < 6) :
    wOdd t (3 + 6 * s + r) = blkOdd (7 + 3 * (s : ℤ)) r := by
  have h1 : 3 + 6 * s + r - 3 = 6 * s + r := by omega
  have h2 : (6 * s + r) / 6 = s := by omega
  have h3 : (6 * s + r) % 6 = r := by omega
  unfold wOdd
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), h1, h2, h3]

lemma wOdd_cap (t : ℕ) : wOdd t (3 + 6 * t + 0) = -(7 + 3 * (t : ℤ)) := by
  unfold wOdd
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]

lemma wOdd_suf {t j : ℕ} (hj : j < 9) : wOdd t (4 + 6 * t + j) = sufOdd j := by
  have h1 : 4 + 6 * t + j - (4 + 6 * t) = j := by omega
  unfold wOdd
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), h1]

lemma wOdd_3 (t : ℕ) : wOdd t (2 + 1) = -7 := by
  rcases Nat.eq_zero_or_pos t with rfl | h
  · unfold wOdd
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega)]
    norm_num
  · unfold wOdd
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    norm_num [blkOdd]

lemma wOdd_next_block {t s : ℕ} (hs : s < t) :
    wOdd t (3 + 6 * s + 5 + 1) = -(10 + 3 * (s : ℤ)) := by
  rcases Nat.lt_or_ge (s + 1) t with h | h
  · rw [show 3 + 6 * s + 5 + 1 = 3 + 6 * (s + 1) + 0 by ring, wOdd_blk h (by norm_num)]
    show -(7 + 3 * ((s : ℤ) + 1)) = _
    ring
  · have hst : s + 1 = t := by omega
    rw [show 3 + 6 * s + 5 + 1 = 3 + 6 * (s + 1) + 0 by ring, hst, wOdd_cap, ← hst]
    push_cast
    ring

lemma kOdd_blk {t s r : ℕ} (hs : s < t) (hr : r < 6) :
    kOdd t (3 + 6 * s + r) = kBlkOdd t s r := by
  have h1 : 3 + 6 * s + r - 3 = 6 * s + r := by omega
  have h2 : (6 * s + r) / 6 = s := by omega
  have h3 : (6 * s + r) % 6 = r := by omega
  unfold kOdd
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), h1, h2, h3]

lemma kOdd_cap (t : ℕ) : kOdd t (3 + 6 * t) = 8 + 3 * t := by
  unfold kOdd
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]

lemma kOdd_suf {t j : ℕ} (hj : j < 8) : kOdd t (4 + 6 * t + j) = kSufOdd t j := by
  have h1 : 4 + 6 * t + j - (4 + 6 * t) = j := by omega
  unfold kOdd
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), h1]

lemma kOdd_0 (t : ℕ) : kOdd t 0 = 2 := rfl
lemma kOdd_1 (t : ℕ) : kOdd t 1 = 6 := rfl
lemma kOdd_2 (t : ℕ) : kOdd t 2 = 7 := rfl

/-- Every position of the odd-chain word lies in one of the six regions. -/
lemma region_odd (t i : ℕ) (hi : i < 12 + 6 * t) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ (∃ s < t, ∃ r < 6, i = 3 + 6 * s + r) ∨ i = 3 + 6 * t
      ∨ (∃ j < 8, i = 4 + 6 * t + j) := by
  rcases Nat.lt_or_ge i 3 with h | h
  · interval_cases i <;> simp
  rcases Nat.lt_or_ge i (3 + 6 * t) with h2 | h2
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨(i - 3) / 6, ?_, (i - 3) % 6, ?_, ?_⟩))) <;> omega
  rcases eq_or_lt_of_le h2 with h3 | h3
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3.symm))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i - (4 + 6 * t), by omega, by omega⟩))))

lemma kOdd_mem (t i : ℕ) (hi : i < 12 + 6 * t) : 2 ≤ kOdd t i ∧ kOdd t i ≤ 13 + 6 * t := by
  rcases region_odd t i hi with rfl | rfl | rfl | ⟨s, hs, r, hr, rfl⟩ | rfl | ⟨j, hj, rfl⟩
  · rw [kOdd_0]; omega
  · rw [kOdd_1]; omega
  · rw [kOdd_2]; omega
  · rw [kOdd_blk hs hr]; interval_cases r <;> simp only [kBlkOdd] <;> omega
  · rw [kOdd_cap]; omega
  · rw [kOdd_suf hj]; interval_cases j <;> simp only [kSufOdd] <;> omega

set_option maxHeartbeats 400000 in
/-- The odd-chain class assignment is injective on the word's positions. -/
lemma kOdd_inj (t i j : ℕ) (hi : i < 12 + 6 * t) (hj : j < 12 + 6 * t)
    (h : kOdd t i = kOdd t j) : i = j := by
  rcases region_odd t i hi with rfl|rfl|rfl|⟨s,hs,r,hr,rfl⟩|rfl|⟨a,ha,rfl⟩ <;>
  rcases region_odd t j hj with rfl|rfl|rfl|⟨s',hs',r',hr',rfl⟩|rfl|⟨b,hb,rfl⟩
  · rfl
  · -- z0 / z1
    rw [kOdd_0, kOdd_1] at h
    omega
  · -- z0 / z2
    rw [kOdd_0, kOdd_2] at h
    omega
  · -- z0 / blk
    rw [kOdd_0, kOdd_blk hs' hr'] at h
    interval_cases r' <;>
      simp only [kBlkOdd] at h <;>
      omega
  · -- z0 / cap
    rw [kOdd_0, kOdd_cap] at h
    omega
  · -- z0 / suf
    rw [kOdd_0, kOdd_suf hb] at h
    interval_cases b <;>
      simp only [kSufOdd] at h <;>
      omega
  · -- z1 / z0
    rw [kOdd_1, kOdd_0] at h
    omega
  · rfl
  · -- z1 / z2
    rw [kOdd_1, kOdd_2] at h
    omega
  · -- z1 / blk
    rw [kOdd_1, kOdd_blk hs' hr'] at h
    interval_cases r' <;>
      simp only [kBlkOdd] at h <;>
      omega
  · -- z1 / cap
    rw [kOdd_1, kOdd_cap] at h
    omega
  · -- z1 / suf
    rw [kOdd_1, kOdd_suf hb] at h
    interval_cases b <;>
      simp only [kSufOdd] at h <;>
      omega
  · -- z2 / z0
    rw [kOdd_2, kOdd_0] at h
    omega
  · -- z2 / z1
    rw [kOdd_2, kOdd_1] at h
    omega
  · rfl
  · -- z2 / blk
    rw [kOdd_2, kOdd_blk hs' hr'] at h
    interval_cases r' <;>
      simp only [kBlkOdd] at h <;>
      omega
  · -- z2 / cap
    rw [kOdd_2, kOdd_cap] at h
    omega
  · -- z2 / suf
    rw [kOdd_2, kOdd_suf hb] at h
    interval_cases b <;>
      simp only [kSufOdd] at h <;>
      omega
  · -- blk / z0
    rw [kOdd_blk hs hr, kOdd_0] at h
    interval_cases r <;>
      simp only [kBlkOdd] at h <;>
      omega
  · -- blk / z1
    rw [kOdd_blk hs hr, kOdd_1] at h
    interval_cases r <;>
      simp only [kBlkOdd] at h <;>
      omega
  · -- blk / z2
    rw [kOdd_blk hs hr, kOdd_2] at h
    interval_cases r <;>
      simp only [kBlkOdd] at h <;>
      omega
  · -- blk / blk
    rw [kOdd_blk hs hr, kOdd_blk hs' hr'] at h
    interval_cases r <;>
      interval_cases r' <;>
      simp only [kBlkOdd] at h <;>
      omega
  · -- blk / cap
    rw [kOdd_blk hs hr, kOdd_cap] at h
    interval_cases r <;>
      simp only [kBlkOdd] at h <;>
      omega
  · -- blk / suf
    rw [kOdd_blk hs hr, kOdd_suf hb] at h
    interval_cases r <;>
      interval_cases b <;>
      simp only [kBlkOdd, kSufOdd] at h <;>
      omega
  · -- cap / z0
    rw [kOdd_cap, kOdd_0] at h
    omega
  · -- cap / z1
    rw [kOdd_cap, kOdd_1] at h
    omega
  · -- cap / z2
    rw [kOdd_cap, kOdd_2] at h
    omega
  · -- cap / blk
    rw [kOdd_cap, kOdd_blk hs' hr'] at h
    interval_cases r' <;>
      simp only [kBlkOdd] at h <;>
      omega
  · rfl
  · -- cap / suf
    rw [kOdd_cap, kOdd_suf hb] at h
    interval_cases b <;>
      simp only [kSufOdd] at h <;>
      omega
  · -- suf / z0
    rw [kOdd_suf ha, kOdd_0] at h
    interval_cases a <;>
      simp only [kSufOdd] at h <;>
      omega
  · -- suf / z1
    rw [kOdd_suf ha, kOdd_1] at h
    interval_cases a <;>
      simp only [kSufOdd] at h <;>
      omega
  · -- suf / z2
    rw [kOdd_suf ha, kOdd_2] at h
    interval_cases a <;>
      simp only [kSufOdd] at h <;>
      omega
  · -- suf / blk
    rw [kOdd_suf ha, kOdd_blk hs' hr'] at h
    interval_cases r' <;>
      interval_cases a <;>
      simp only [kBlkOdd, kSufOdd] at h <;>
      omega
  · -- suf / cap
    rw [kOdd_suf ha, kOdd_cap] at h
    interval_cases a <;>
      simp only [kSufOdd] at h <;>
      omega
  · -- suf / suf
    rw [kOdd_suf ha, kOdd_suf hb] at h
    interval_cases a <;>
      interval_cases b <;>
      simp only [kSufOdd] at h <;>
      omega

set_option maxHeartbeats 400000 in
lemma real_odd (t i : ℕ) (hi : i < 12 + 6*t) :
    RealizesClass (15+6*t) (kOdd t i)
      ((wOdd t i : ℤ) : ZMod (15+6*t)) ((wOdd t (i+1) : ℤ) : ZMod (15+6*t)) := by
  have hn : ((15 + 6*t : ℕ) : ZMod (15+6*t)) = 0 := ZMod.natCast_self _
  push_cast at hn
  rcases region_odd t i hi with rfl|rfl|rfl|⟨s,hs,r,hr,rfl⟩|rfl|⟨a,ha,rfl⟩
  · rw [show kOdd t 0 = 2 from rfl, show wOdd t 0 = 2 from rfl,
        show wOdd t (0+1) = -1 from rfl]
    refine realizes_II _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
  · rw [show kOdd t 1 = 6 from rfl, show wOdd t 1 = -1 from rfl,
        show wOdd t (1+1) = 6 from rfl]
    refine realizes_III _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
  · rw [show kOdd t 2 = 7 from rfl, show wOdd t 2 = 6 from rfl, wOdd_3]
    refine realizes_IV _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
  · have hle1 : 3*s ≤ 6+6*t := by omega
    have hle2 : 3*s ≤ 8+6*t := by omega
    have hle3 : 3*s ≤ 7+6*t := by omega
    interval_cases r
    · rw [kOdd_blk hs (by norm_num), wOdd_blk hs (by norm_num),
        show 3+6*s+0+1 = 3+6*s+1 by ring, wOdd_blk hs (by norm_num)]
      show RealizesClass _ (8+3*s) ((-(7+3*(s:ℤ)) : ℤ) : ZMod (15+6*t)) (((-1 : ℤ)) : ZMod (15+6*t))
      refine realizes_VI _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kOdd_blk hs (by norm_num), wOdd_blk hs (by norm_num),
        show 3+6*s+1+1 = 3+6*s+2 by ring, wOdd_blk hs (by norm_num)]
      show RealizesClass _ (9+3*s) (((-1:ℤ)) : ZMod (15+6*t)) (((7+3*(s:ℤ)+2 : ℤ)) : ZMod (15+6*t))
      refine realizes_III _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kOdd_blk hs (by norm_num), wOdd_blk hs (by norm_num),
        show 3+6*s+2+1 = 3+6*s+3 by ring, wOdd_blk hs (by norm_num)]
      show RealizesClass _ (6+6*t-3*s) (((7+3*(s:ℤ)+2 : ℤ)) : ZMod (15+6*t)) (((1:ℤ)) : ZMod (15+6*t))
      refine realizes_V _ _ _ _ ?_ ?_ <;> push_cast [Nat.cast_sub hle1] <;> modclose hn
    · rw [kOdd_blk hs (by norm_num), wOdd_blk hs (by norm_num),
        show 3+6*s+3+1 = 3+6*s+4 by ring, wOdd_blk hs (by norm_num)]
      show RealizesClass _ (8+6*t-3*s) (((1:ℤ)) : ZMod (15+6*t)) (((-(7+3*(s:ℤ)+1) : ℤ)) : ZMod (15+6*t))
      refine realizes_I _ _ _ _ ?_ ?_ <;> push_cast [Nat.cast_sub hle2] <;> modclose hn
    · rw [kOdd_blk hs (by norm_num), wOdd_blk hs (by norm_num),
        show 3+6*s+4+1 = 3+6*s+5 by ring, wOdd_blk hs (by norm_num)]
      show RealizesClass _ (7+6*t-3*s) (((-(7+3*(s:ℤ)+1) : ℤ)) : ZMod (15+6*t))
        (((7+3*(s:ℤ)+2 : ℤ)) : ZMod (15+6*t))
      refine realizes_II _ _ _ _ ?_ ?_ <;> push_cast [Nat.cast_sub hle3] <;> modclose hn
    · rw [kOdd_blk hs (by norm_num), wOdd_blk hs (by norm_num), wOdd_next_block hs]
      show RealizesClass _ (10+3*s) (((7+3*(s:ℤ)+2 : ℤ)) : ZMod (15+6*t))
        (((-(10+3*(s:ℤ)) : ℤ)) : ZMod (15+6*t))
      refine realizes_IV _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
  · rw [kOdd_cap, show 3+6*t = 3+6*t+0 by ring, wOdd_cap,
      show 3+6*t+0+1 = 4+6*t+0 by ring, wOdd_suf (by norm_num)]
    show RealizesClass _ (8+3*t) _ (((-1 : ℤ)) : ZMod (15+6*t))
    refine realizes_VI _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
  · interval_cases a
    · rw [kOdd_suf (by norm_num), wOdd_suf (by norm_num),
        show 4+6*t+0+1 = 4+6*t+1 by ring, wOdd_suf (by norm_num)]
      show RealizesClass _ (12+6*t) (((-1:ℤ)) : ZMod (15+6*t)) (((-3:ℤ)) : ZMod (15+6*t))
      refine realizes_III _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kOdd_suf (by norm_num), wOdd_suf (by norm_num),
        show 4+6*t+1+1 = 4+6*t+2 by ring, wOdd_suf (by norm_num)]
      show RealizesClass _ 3 (((-3:ℤ)) : ZMod (15+6*t)) (((1:ℤ)) : ZMod (15+6*t))
      refine realizes_V _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kOdd_suf (by norm_num), wOdd_suf (by norm_num),
        show 4+6*t+2+1 = 4+6*t+3 by ring, wOdd_suf (by norm_num)]
      show RealizesClass _ (11+6*t) (((1:ℤ)) : ZMod (15+6*t)) (((-5:ℤ)) : ZMod (15+6*t))
      refine realizes_I _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kOdd_suf (by norm_num), wOdd_suf (by norm_num),
        show 4+6*t+3+1 = 4+6*t+4 by ring, wOdd_suf (by norm_num)]
      show RealizesClass _ (10+6*t) (((-5:ℤ)) : ZMod (15+6*t)) (((6:ℤ)) : ZMod (15+6*t))
      refine realizes_II _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kOdd_suf (by norm_num), wOdd_suf (by norm_num),
        show 4+6*t+4+1 = 4+6*t+5 by ring, wOdd_suf (by norm_num)]
      show RealizesClass _ (9+6*t) (((6:ℤ)) : ZMod (15+6*t)) (((1:ℤ)) : ZMod (15+6*t))
      refine realizes_V _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kOdd_suf (by norm_num), wOdd_suf (by norm_num),
        show 4+6*t+5+1 = 4+6*t+6 by ring, wOdd_suf (by norm_num)]
      show RealizesClass _ 5 (((1:ℤ)) : ZMod (15+6*t)) (((4:ℤ)) : ZMod (15+6*t))
      refine realizes_I _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kOdd_suf (by norm_num), wOdd_suf (by norm_num),
        show 4+6*t+6+1 = 4+6*t+7 by ring, wOdd_suf (by norm_num)]
      show RealizesClass _ 4 (((4:ℤ)) : ZMod (15+6*t)) (((-3:ℤ)) : ZMod (15+6*t))
      refine realizes_II _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kOdd_suf (by norm_num), wOdd_suf (by norm_num),
        show 4+6*t+7+1 = 4+6*t+8 by ring, wOdd_suf (by norm_num)]
      show RealizesClass _ (13+6*t) (((-3:ℤ)) : ZMod (15+6*t)) (((2:ℤ)) : ZMod (15+6*t))
      refine realizes_IV _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn

lemma blkOdd_sum (L : ℤ) : ∑ r ∈ Finset.range 6, blkOdd L r = 3 := by
  simp [Finset.sum_range_succ, blkOdd]; ring

lemma wOdd_block_sum (t : ℕ) :
    ∀ u ≤ t, ∑ j ∈ Finset.range (6 * u), wOdd t (3 + j) = 3 * u := by
  intro u
  induction u with
  | zero => simp
  | succ u ih =>
    intro hu
    rw [show 6 * (u + 1) = 6 * u + 6 by ring, Finset.sum_range_add, ih (by omega)]
    have hblk : ∑ x ∈ Finset.range 6, wOdd t (3 + (6 * u + x)) = 3 := by
      rw [← blkOdd_sum (7 + 3 * (u : ℤ))]
      refine Finset.sum_congr rfl fun r hr => ?_
      simp only [Finset.mem_range] at hr
      rw [show 3 + (6 * u + r) = 3 + 6 * u + r by ring]
      exact wOdd_blk (by omega) hr
    rw [hblk]
    push_cast
    ring

/-- The odd-chain word has integer sum `0`, so it closes up at every `n`. -/
lemma wOdd_total (t : ℕ) : ∑ j ∈ Finset.range (12 + 6 * t), wOdd t j = 0 := by
  rw [show 12 + 6 * t = 3 + (6 * t + 9) by ring, Finset.sum_range_add]
  rw [show ∑ j ∈ Finset.range 3, wOdd t j = 7 by simp [Finset.sum_range_succ, wOdd]]
  have e2 : ∑ j ∈ Finset.range (6 * t + 9), wOdd t (3 + j)
      = (∑ j ∈ Finset.range (6 * t), wOdd t (3 + j))
        + ∑ j ∈ Finset.range 9, wOdd t (3 + (6 * t + j)) := Finset.sum_range_add _ _ _
  rw [e2, wOdd_block_sum t t le_rfl]
  have e3 : ∑ j ∈ Finset.range 9, wOdd t (3 + (6 * t + j)) = -(7 + 3 * (t : ℤ)) := by
    rw [Finset.sum_range_succ' _ 8, show 3 + (6 * t + 0) = 3 + 6 * t + 0 by ring, wOdd_cap]
    have e4 : ∀ j ∈ Finset.range 8, wOdd t (3 + (6 * t + (j + 1))) = sufOdd j := by
      intro j hj
      simp only [Finset.mem_range] at hj
      rw [show 3 + (6 * t + (j + 1)) = 4 + 6 * t + j by ring]
      exact wOdd_suf (by omega)
    rw [Finset.sum_congr rfl e4]
    simp [Finset.sum_range_succ, sufOdd]
  rw [e3]
  ring

/-! ### Stage 2A — the even chain `n = 18 + 6t`

Word (signed): `[2, -1, 9+3t]`, then `t` tails `[L+2, -1, -L, 1, L+1, -L]` with
`L = 6 + 3t - 3u` running downwards, then the fixed twelve-entry suffix
`[8, -7, 1, 5, -4, 1, -6, 7, 1, -3, 4, 1]`.  Its integer sum is `n`. -/

/-- The six entries of an even-chain tail with head level `L`. -/
def tlEven (L : ℤ) : ℕ → ℤ
  | 0 => L + 2 | 1 => -1 | 2 => -L | 3 => 1 | 4 => L + 1 | _ => -L

/-- The twelve-entry suffix of the even-chain word; index `12` is the cyclic
wrap back to the first entry. -/
def sufEven : ℕ → ℤ
  | 0 => 8 | 1 => -7 | 2 => 1 | 3 => 5 | 4 => -4 | 5 => 1 | 6 => -6 | 7 => 7 | 8 => 1
  | 9 => -3 | 10 => 4 | 11 => 1 | _ => 2

/-- The even-chain step word at `n = 18 + 6t`. -/
def wEven (t i : ℕ) : ℤ :=
  if i = 0 then 2 else if i = 1 then -1 else if i = 2 then 9 + 3 * (t : ℤ)
  else if i < 3 + 6 * t then tlEven (6 + 3 * (t : ℤ) - 3 * (((i - 3) / 6 : ℕ) : ℤ)) ((i - 3) % 6)
  else sufEven (i - (3 + 6 * t))

/-- The classes realized inside an even-chain tail. -/
def kTlEven (t u : ℕ) : ℕ → ℕ
  | 0 => 11 + 3 * t + 3 * u | 1 => 12 + 3 * t + 3 * u | 2 => 6 + 3 * t - 3 * u
  | 3 => 8 + 3 * t - 3 * u | 4 => 7 + 3 * t - 3 * u | _ => 13 + 3 * t + 3 * u

/-- The classes realized in the even-chain suffix. -/
def kSufEven (t : ℕ) : ℕ → ℕ
  | 0 => 8 | 1 => 7 | 2 => 6 | 3 => 5 | 4 => 4 | 5 => 13 + 6 * t | 6 => 12 + 6 * t
  | 7 => 11 + 6 * t | 8 => 16 + 6 * t | 9 => 15 + 6 * t | 10 => 14 + 6 * t | _ => 3

/-- The class realized at position `i` of the even-chain word. -/
def kEven (t i : ℕ) : ℕ :=
  if i = 0 then 2 else if i = 1 then 9 + 3 * t else if i = 2 then 10 + 3 * t
  else if i < 3 + 6 * t then kTlEven t ((i - 3) / 6) ((i - 3) % 6)
  else kSufEven t (i - (3 + 6 * t))

lemma wEven_tl {t u r : ℕ} (hu : u < t) (hr : r < 6) :
    wEven t (3 + 6 * u + r) = tlEven (6 + 3 * (t : ℤ) - 3 * (u : ℤ)) r := by
  have h1 : 3 + 6 * u + r - 3 = 6 * u + r := by omega
  have h2 : (6 * u + r) / 6 = u := by omega
  have h3 : (6 * u + r) % 6 = r := by omega
  unfold wEven
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), h1, h2, h3]

lemma wEven_suf {t j : ℕ} (hj : j < 13) : wEven t (3 + 6 * t + j) = sufEven j := by
  have h1 : 3 + 6 * t + j - (3 + 6 * t) = j := by omega
  unfold wEven
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), h1]

lemma wEven_3 (t : ℕ) : wEven t (2 + 1) = 8 + 3 * (t : ℤ) := by
  rcases Nat.eq_zero_or_pos t with rfl | h
  · rw [show (2 : ℕ) + 1 = 3 + 6 * 0 + 0 by norm_num, wEven_suf (by norm_num)]
    norm_num [sufEven]
  · rw [show (2 : ℕ) + 1 = 3 + 6 * 0 + 0 by norm_num, wEven_tl (by omega) (by norm_num)]
    show 6 + 3 * (t : ℤ) - 3 * ((0 : ℕ) : ℤ) + 2 = _
    push_cast
    ring

lemma wEven_next_tail {t u : ℕ} (hu : u < t) :
    wEven t (3 + 6 * u + 5 + 1) = 5 + 3 * (t : ℤ) - 3 * (u : ℤ) := by
  rcases Nat.lt_or_ge (u + 1) t with h | h
  · rw [show 3 + 6 * u + 5 + 1 = 3 + 6 * (u + 1) + 0 by ring, wEven_tl h (by norm_num)]
    show 6 + 3 * (t : ℤ) - 3 * (((u + 1 : ℕ)) : ℤ) + 2 = _
    push_cast
    ring
  · have hut : u + 1 = t := by omega
    rw [show 3 + 6 * u + 5 + 1 = 3 + 6 * (u + 1) + 0 by ring, hut, wEven_suf (by norm_num)]
    show (8 : ℤ) = _
    rw [← hut]
    push_cast
    ring

lemma kEven_tl {t u r : ℕ} (hu : u < t) (hr : r < 6) :
    kEven t (3 + 6 * u + r) = kTlEven t u r := by
  have h1 : 3 + 6 * u + r - 3 = 6 * u + r := by omega
  have h2 : (6 * u + r) / 6 = u := by omega
  have h3 : (6 * u + r) % 6 = r := by omega
  unfold kEven
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), h1, h2, h3]

lemma kEven_suf {t j : ℕ} (hj : j < 12) : kEven t (3 + 6 * t + j) = kSufEven t j := by
  have h1 : 3 + 6 * t + j - (3 + 6 * t) = j := by omega
  unfold kEven
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), h1]

lemma kEven_0 (t : ℕ) : kEven t 0 = 2 := rfl
lemma kEven_1 (t : ℕ) : kEven t 1 = 9 + 3 * t := rfl
lemma kEven_2 (t : ℕ) : kEven t 2 = 10 + 3 * t := rfl

/-- Every position of the even-chain word lies in one of the five regions. -/
lemma region_even (t i : ℕ) (hi : i < 15 + 6 * t) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ (∃ u < t, ∃ r < 6, i = 3 + 6 * u + r)
      ∨ (∃ j < 12, i = 3 + 6 * t + j) := by
  rcases Nat.lt_or_ge i 3 with h | h
  · interval_cases i <;> simp
  rcases Nat.lt_or_ge i (3 + 6 * t) with h2 | h2
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨(i - 3) / 6, ?_, (i - 3) % 6, ?_, ?_⟩))) <;> omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i - (3 + 6 * t), by omega, by omega⟩)))

lemma kEven_mem (t i : ℕ) (hi : i < 15 + 6 * t) : 2 ≤ kEven t i ∧ kEven t i ≤ 16 + 6 * t := by
  rcases region_even t i hi with rfl | rfl | rfl | ⟨u, hu, r, hr, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [kEven_0]; omega
  · rw [kEven_1]; omega
  · rw [kEven_2]; omega
  · rw [kEven_tl hu hr]; interval_cases r <;> simp only [kTlEven] <;> omega
  · rw [kEven_suf hj]; interval_cases j <;> simp only [kSufEven] <;> omega

set_option maxHeartbeats 400000 in
/-- The even-chain class assignment is injective on the word's positions. -/
lemma kEven_inj (t i j : ℕ) (hi : i < 15 + 6 * t) (hj : j < 15 + 6 * t)
    (h : kEven t i = kEven t j) : i = j := by
  rcases region_even t i hi with rfl|rfl|rfl|⟨u,hu,r,hr,rfl⟩|⟨a,ha,rfl⟩ <;>
  rcases region_even t j hj with rfl|rfl|rfl|⟨u',hu',r',hr',rfl⟩|⟨b,hb,rfl⟩
  · rfl
  · -- z0 / z1
    rw [kEven_0, kEven_1] at h
    omega
  · -- z0 / z2
    rw [kEven_0, kEven_2] at h
    omega
  · -- z0 / tl
    rw [kEven_0, kEven_tl hu' hr'] at h
    interval_cases r' <;>
      simp only [kTlEven] at h <;>
      omega
  · -- z0 / suf
    rw [kEven_0, kEven_suf hb] at h
    interval_cases b <;>
      simp only [kSufEven] at h <;>
      omega
  · -- z1 / z0
    rw [kEven_1, kEven_0] at h
    omega
  · rfl
  · -- z1 / z2
    rw [kEven_1, kEven_2] at h
    omega
  · -- z1 / tl
    rw [kEven_1, kEven_tl hu' hr'] at h
    interval_cases r' <;>
      simp only [kTlEven] at h <;>
      omega
  · -- z1 / suf
    rw [kEven_1, kEven_suf hb] at h
    interval_cases b <;>
      simp only [kSufEven] at h <;>
      omega
  · -- z2 / z0
    rw [kEven_2, kEven_0] at h
    omega
  · -- z2 / z1
    rw [kEven_2, kEven_1] at h
    omega
  · rfl
  · -- z2 / tl
    rw [kEven_2, kEven_tl hu' hr'] at h
    interval_cases r' <;>
      simp only [kTlEven] at h <;>
      omega
  · -- z2 / suf
    rw [kEven_2, kEven_suf hb] at h
    interval_cases b <;>
      simp only [kSufEven] at h <;>
      omega
  · -- tl / z0
    rw [kEven_tl hu hr, kEven_0] at h
    interval_cases r <;>
      simp only [kTlEven] at h <;>
      omega
  · -- tl / z1
    rw [kEven_tl hu hr, kEven_1] at h
    interval_cases r <;>
      simp only [kTlEven] at h <;>
      omega
  · -- tl / z2
    rw [kEven_tl hu hr, kEven_2] at h
    interval_cases r <;>
      simp only [kTlEven] at h <;>
      omega
  · -- tl / tl
    rw [kEven_tl hu hr, kEven_tl hu' hr'] at h
    interval_cases r <;>
      interval_cases r' <;>
      simp only [kTlEven] at h <;>
      omega
  · -- tl / suf
    rw [kEven_tl hu hr, kEven_suf hb] at h
    interval_cases r <;>
      interval_cases b <;>
      simp only [kTlEven, kSufEven] at h <;>
      omega
  · -- suf / z0
    rw [kEven_suf ha, kEven_0] at h
    interval_cases a <;>
      simp only [kSufEven] at h <;>
      omega
  · -- suf / z1
    rw [kEven_suf ha, kEven_1] at h
    interval_cases a <;>
      simp only [kSufEven] at h <;>
      omega
  · -- suf / z2
    rw [kEven_suf ha, kEven_2] at h
    interval_cases a <;>
      simp only [kSufEven] at h <;>
      omega
  · -- suf / tl
    rw [kEven_suf ha, kEven_tl hu' hr'] at h
    interval_cases r' <;>
      interval_cases a <;>
      simp only [kTlEven, kSufEven] at h <;>
      omega
  · -- suf / suf
    rw [kEven_suf ha, kEven_suf hb] at h
    interval_cases a <;>
      interval_cases b <;>
      simp only [kSufEven] at h <;>
      omega

lemma tlEven_sum (L : ℤ) : ∑ r ∈ Finset.range 6, tlEven L r = 3 := by
  simp [Finset.sum_range_succ, tlEven]; ring

lemma wEven_tail_sum (t : ℕ) :
    ∀ v ≤ t, ∑ j ∈ Finset.range (6 * v), wEven t (3 + j) = 3 * v := by
  intro v
  induction v with
  | zero => simp
  | succ v ih =>
    intro hv
    rw [show 6 * (v + 1) = 6 * v + 6 by ring, Finset.sum_range_add, ih (by omega)]
    have htl : ∑ x ∈ Finset.range 6, wEven t (3 + (6 * v + x)) = 3 := by
      rw [← tlEven_sum (6 + 3 * (t : ℤ) - 3 * (v : ℤ))]
      refine Finset.sum_congr rfl fun r hr => ?_
      simp only [Finset.mem_range] at hr
      rw [show 3 + (6 * v + r) = 3 + 6 * v + r by ring]
      exact wEven_tl (by omega) hr
    rw [htl]
    push_cast
    ring

/-- The even-chain word has integer sum `n = 18 + 6t`, so it closes up mod `n`. -/
lemma wEven_total (t : ℕ) :
    ∑ j ∈ Finset.range (15 + 6 * t), wEven t j = 18 + 6 * (t : ℤ) := by
  rw [show 15 + 6 * t = 3 + (6 * t + 12) by ring, Finset.sum_range_add]
  rw [show ∑ j ∈ Finset.range 3, wEven t j = 10 + 3 * (t : ℤ) by
    simp [Finset.sum_range_succ, wEven]; ring]
  have e2 : ∑ j ∈ Finset.range (6 * t + 12), wEven t (3 + j)
      = (∑ j ∈ Finset.range (6 * t), wEven t (3 + j))
        + ∑ j ∈ Finset.range 12, wEven t (3 + (6 * t + j)) := Finset.sum_range_add _ _ _
  rw [e2, wEven_tail_sum t t le_rfl]
  have e3 : ∑ j ∈ Finset.range 12, wEven t (3 + (6 * t + j)) = 8 := by
    have e4 : ∀ j ∈ Finset.range 12, wEven t (3 + (6 * t + j)) = sufEven j := by
      intro j hj
      simp only [Finset.mem_range] at hj
      rw [show 3 + (6 * t + j) = 3 + 6 * t + j by ring]
      exact wEven_suf (by omega)
    rw [Finset.sum_congr rfl e4]
    simp [Finset.sum_range_succ, sufEven]
  rw [e3]
  ring

set_option maxHeartbeats 400000 in
lemma real_even (t i : ℕ) (hi : i < 15 + 6*t) :
    RealizesClass (18+6*t) (kEven t i)
      ((wEven t i : ℤ) : ZMod (18+6*t)) ((wEven t (i+1) : ℤ) : ZMod (18+6*t)) := by
  have hn : ((18 + 6*t : ℕ) : ZMod (18+6*t)) = 0 := ZMod.natCast_self _
  push_cast at hn
  rcases region_even t i hi with rfl|rfl|rfl|⟨u,hu,r,hr,rfl⟩|⟨a,ha,rfl⟩
  · rw [show kEven t 0 = 2 from rfl, show wEven t 0 = 2 from rfl,
        show wEven t (0+1) = -1 from rfl]
    refine realizes_II _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
  · rw [show kEven t 1 = 9+3*t from rfl, show wEven t 1 = -1 from rfl,
        show wEven t (1+1) = 9+3*(t:ℤ) from rfl]
    refine realizes_III _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
  · rw [show kEven t 2 = 10+3*t from rfl, show wEven t 2 = 9+3*(t:ℤ) from rfl, wEven_3]
    refine realizes_IV _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
  · have hle1 : 3*u ≤ 6+3*t := by omega
    have hle2 : 3*u ≤ 8+3*t := by omega
    have hle3 : 3*u ≤ 7+3*t := by omega
    interval_cases r
    · rw [kEven_tl hu (by norm_num), wEven_tl hu (by norm_num),
        show 3+6*u+0+1 = 3+6*u+1 by ring, wEven_tl hu (by norm_num)]
      show RealizesClass _ (11+3*t+3*u) (((6+3*(t:ℤ)-3*(u:ℤ)+2 : ℤ)) : ZMod (18+6*t))
        (((-1:ℤ)) : ZMod (18+6*t))
      refine realizes_VI _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kEven_tl hu (by norm_num), wEven_tl hu (by norm_num),
        show 3+6*u+1+1 = 3+6*u+2 by ring, wEven_tl hu (by norm_num)]
      show RealizesClass _ (12+3*t+3*u) (((-1:ℤ)) : ZMod (18+6*t))
        (((-(6+3*(t:ℤ)-3*(u:ℤ)) : ℤ)) : ZMod (18+6*t))
      refine realizes_III _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kEven_tl hu (by norm_num), wEven_tl hu (by norm_num),
        show 3+6*u+2+1 = 3+6*u+3 by ring, wEven_tl hu (by norm_num)]
      show RealizesClass _ (6+3*t-3*u) (((-(6+3*(t:ℤ)-3*(u:ℤ)) : ℤ)) : ZMod (18+6*t))
        (((1:ℤ)) : ZMod (18+6*t))
      refine realizes_V _ _ _ _ ?_ ?_ <;> push_cast [Nat.cast_sub hle1] <;> modclose hn
    · rw [kEven_tl hu (by norm_num), wEven_tl hu (by norm_num),
        show 3+6*u+3+1 = 3+6*u+4 by ring, wEven_tl hu (by norm_num)]
      show RealizesClass _ (8+3*t-3*u) (((1:ℤ)) : ZMod (18+6*t))
        (((6+3*(t:ℤ)-3*(u:ℤ)+1 : ℤ)) : ZMod (18+6*t))
      refine realizes_I _ _ _ _ ?_ ?_ <;> push_cast [Nat.cast_sub hle2] <;> modclose hn
    · rw [kEven_tl hu (by norm_num), wEven_tl hu (by norm_num),
        show 3+6*u+4+1 = 3+6*u+5 by ring, wEven_tl hu (by norm_num)]
      show RealizesClass _ (7+3*t-3*u) (((6+3*(t:ℤ)-3*(u:ℤ)+1 : ℤ)) : ZMod (18+6*t))
        (((-(6+3*(t:ℤ)-3*(u:ℤ)) : ℤ)) : ZMod (18+6*t))
      refine realizes_II _ _ _ _ ?_ ?_ <;> push_cast [Nat.cast_sub hle3] <;> modclose hn
    · rw [kEven_tl hu (by norm_num), wEven_tl hu (by norm_num), wEven_next_tail hu]
      show RealizesClass _ (13+3*t+3*u) (((-(6+3*(t:ℤ)-3*(u:ℤ)) : ℤ)) : ZMod (18+6*t))
        (((5+3*(t:ℤ)-3*(u:ℤ) : ℤ)) : ZMod (18+6*t))
      refine realizes_IV _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
  · interval_cases a
    · rw [kEven_suf (by norm_num), wEven_suf (by norm_num),
        show 3+6*t+0+1 = 3+6*t+1 by ring, wEven_suf (by norm_num)]
      show RealizesClass _ 8 (((8:ℤ)) : ZMod (18+6*t)) (((-7:ℤ)) : ZMod (18+6*t))
      refine realizes_II _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kEven_suf (by norm_num), wEven_suf (by norm_num),
        show 3+6*t+1+1 = 3+6*t+2 by ring, wEven_suf (by norm_num)]
      show RealizesClass _ 7 (((-7:ℤ)) : ZMod (18+6*t)) (((1:ℤ)) : ZMod (18+6*t))
      refine realizes_V _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kEven_suf (by norm_num), wEven_suf (by norm_num),
        show 3+6*t+2+1 = 3+6*t+3 by ring, wEven_suf (by norm_num)]
      show RealizesClass _ 6 (((1:ℤ)) : ZMod (18+6*t)) (((5:ℤ)) : ZMod (18+6*t))
      refine realizes_I _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kEven_suf (by norm_num), wEven_suf (by norm_num),
        show 3+6*t+3+1 = 3+6*t+4 by ring, wEven_suf (by norm_num)]
      show RealizesClass _ 5 (((5:ℤ)) : ZMod (18+6*t)) (((-4:ℤ)) : ZMod (18+6*t))
      refine realizes_II _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kEven_suf (by norm_num), wEven_suf (by norm_num),
        show 3+6*t+4+1 = 3+6*t+5 by ring, wEven_suf (by norm_num)]
      show RealizesClass _ 4 (((-4:ℤ)) : ZMod (18+6*t)) (((1:ℤ)) : ZMod (18+6*t))
      refine realizes_V _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kEven_suf (by norm_num), wEven_suf (by norm_num),
        show 3+6*t+5+1 = 3+6*t+6 by ring, wEven_suf (by norm_num)]
      show RealizesClass _ (13+6*t) (((1:ℤ)) : ZMod (18+6*t)) (((-6:ℤ)) : ZMod (18+6*t))
      refine realizes_I _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kEven_suf (by norm_num), wEven_suf (by norm_num),
        show 3+6*t+6+1 = 3+6*t+7 by ring, wEven_suf (by norm_num)]
      show RealizesClass _ (12+6*t) (((-6:ℤ)) : ZMod (18+6*t)) (((7:ℤ)) : ZMod (18+6*t))
      refine realizes_II _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kEven_suf (by norm_num), wEven_suf (by norm_num),
        show 3+6*t+7+1 = 3+6*t+8 by ring, wEven_suf (by norm_num)]
      show RealizesClass _ (11+6*t) (((7:ℤ)) : ZMod (18+6*t)) (((1:ℤ)) : ZMod (18+6*t))
      refine realizes_V _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kEven_suf (by norm_num), wEven_suf (by norm_num),
        show 3+6*t+8+1 = 3+6*t+9 by ring, wEven_suf (by norm_num)]
      show RealizesClass _ (16+6*t) (((1:ℤ)) : ZMod (18+6*t)) (((-3:ℤ)) : ZMod (18+6*t))
      refine realizes_I _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kEven_suf (by norm_num), wEven_suf (by norm_num),
        show 3+6*t+9+1 = 3+6*t+10 by ring, wEven_suf (by norm_num)]
      show RealizesClass _ (15+6*t) (((-3:ℤ)) : ZMod (18+6*t)) (((4:ℤ)) : ZMod (18+6*t))
      refine realizes_II _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kEven_suf (by norm_num), wEven_suf (by norm_num),
        show 3+6*t+10+1 = 3+6*t+11 by ring, wEven_suf (by norm_num)]
      show RealizesClass _ (14+6*t) (((4:ℤ)) : ZMod (18+6*t)) (((1:ℤ)) : ZMod (18+6*t))
      refine realizes_V _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn
    · rw [kEven_suf (by norm_num), wEven_suf (by norm_num),
        show 3+6*t+11+1 = 3+6*t+12 by ring, wEven_suf (by norm_num)]
      show RealizesClass _ 3 (((1:ℤ)) : ZMod (18+6*t)) (((2:ℤ)) : ZMod (18+6*t))
      refine realizes_I _ _ _ _ ?_ ?_ <;> push_cast <;> modclose hn

/-! ### Stage 2A — assembling the two chains -/

/-- Every `n ≡ 3 (mod 6)` with `n ≥ 15` carries a zigzag pitch cycle. -/
theorem exists_zigzag_odd_chain (t : ℕ) :
    ∃ c : ZMod (15 + 6 * t - 3) → ZMod (15 + 6 * t),
      IsCycle (15 + 6 * t) c ∧ IsZigzag (15 + 6 * t) (stepsOf (15 + 6 * t) c) := by
  have hm : 15 + 6 * t - 3 = 12 + 6 * t := by omega
  have hm2 : 15 + 6 * t - 2 = 13 + 6 * t := by omega
  refine exists_zigzag_of_word (15 + 6 * t) (by omega) (wOdd t) (kOdd t) ?_ ?_ ?_ ?_ ?_ rfl ?_
  · rw [hm, wOdd_total]; norm_num
  · rw [hm, show 12 + 6 * t = 4 + 6 * t + 8 by ring, wOdd_suf (by norm_num)]; rfl
  · rw [hm, hm2]; exact fun i hi => kOdd_mem t i hi
  · rw [hm]; exact fun i hi j hj h => kOdd_inj t i j hi hj h
  · rw [hm]; exact fun i hi => real_odd t i hi
  · norm_num [show wOdd t 0 = 2 from rfl]

/-- Every `n ≡ 0 (mod 6)` with `n ≥ 18` carries a zigzag pitch cycle. -/
theorem exists_zigzag_even_chain (t : ℕ) :
    ∃ c : ZMod (18 + 6 * t - 3) → ZMod (18 + 6 * t),
      IsCycle (18 + 6 * t) c ∧ IsZigzag (18 + 6 * t) (stepsOf (18 + 6 * t) c) := by
  have hm : 18 + 6 * t - 3 = 15 + 6 * t := by omega
  have hm2 : 18 + 6 * t - 2 = 16 + 6 * t := by omega
  refine exists_zigzag_of_word (18 + 6 * t) (by omega) (wEven t) (kEven t) ?_ ?_ ?_ ?_ ?_ rfl ?_
  · rw [hm, wEven_total]
    have : ((18 + 6 * t : ℕ) : ZMod (18 + 6 * t)) = 0 := ZMod.natCast_self _
    push_cast at this ⊢
    linear_combination this
  · rw [hm, show 15 + 6 * t = 3 + 6 * t + 12 by ring, wEven_suf (by norm_num)]; rfl
  · rw [hm, hm2]; exact fun i hi => kEven_mem t i hi
  · rw [hm]; exact fun i hi j hj h => kEven_inj t i j hi hj h
  · rw [hm]; exact fun i hi => real_even t i hi
  · norm_num [show wEven t 0 = 2 from rfl]

/-- **Existence.**  For every `n ≥ 8` with `3 ∣ n` and
`n ≠ 12` there is a zigzag pitch cycle: `n = 9` is the explicit witness,
`n ≡ 3 (mod 6)` is the odd chain and `n ≡ 0 (mod 6)` the even chain. -/
theorem exists_zigzag_of_three_dvd (n : ℕ) (hn : 8 ≤ n) (h3 : 3 ∣ n) (h12 : n ≠ 12) :
    ∃ c : ZMod (n - 3) → ZMod n, IsCycle n c ∧ IsZigzag n (stepsOf n c) := by
  rcases eq_or_ne n 9 with rfl | h9
  · exact exists_zigzag_nine
  have hmod : n % 6 = 0 ∨ n % 6 = 3 := by omega
  rcases hmod with h | h
  · obtain ⟨t, rfl⟩ : ∃ t, n = 18 + 6 * t := ⟨(n - 18) / 6, by omega⟩
    exact exists_zigzag_even_chain t
  · obtain ⟨t, rfl⟩ : ∃ t, n = 15 + 6 * t := ⟨(n - 15) / 6, by omega⟩
    exact exists_zigzag_odd_chain t

end Phase2

/-- **Full classification.**  Full classification (paper Theorem 8.3):
zigzag pitch cycles exist iff 3 ∣ n and n ∉ {6, 12}, for n ≥ 8.
Forward direction from `cycle_zigzag_three_dvd`, `twelve_no_zigzag`;
reverse from `exists_zigzag_of_three_dvd`: the n = 9 witness together with
the two closed-form chains of §7. -/
theorem zigzag_classification (n : ℕ) (hn : 8 ≤ n) :
    (∃ c : ZMod (n - 3) → ZMod n, IsCycle n c ∧ IsZigzag n (stepsOf n c))
      ↔ (3 ∣ n ∧ n ≠ 12) := by
  constructor
  · rintro ⟨c, hc, hz⟩
    refine ⟨cycle_zigzag_three_dvd n (by omega) c hc hz, ?_⟩
    rintro rfl
    exact twelve_no_zigzag c hc hz
  · rintro ⟨h3, h12⟩
    exact exists_zigzag_of_three_dvd n hn h3 h12
end

/- ==================== ATTIC: QUARANTINED DEAD ENDS ==================== -/

end MZP
