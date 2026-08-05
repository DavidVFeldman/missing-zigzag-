# Missing Zigzag formalization — status

Date: 2026-08-04 (UTC), round 5 (Phase 2).

## Headline

`lake build` **succeeds** (8027 jobs, `Mzp` elaboration 1670 s) and
`Mzp.lean` is now **sorry-free**: `grep -n sorry Mzp.lean` matches only the
prose of the file header.  Phase 2 (SORRY-15, the existence direction of
`zigzag_classification`) is **closed**, by the closed-form word route of
PHASE2.md Stage 2A.  The axiom audit below shows only the standard axioms
everywhere except the accepted twelve-tone `native_decide` certificate
(`Lean.ofReduceBool` / `Lean.trustCompiler`), which `zigzag_classification`
inherits through `twelve_no_zigzag`.  `sorryAx` no longer occurs anywhere.

## Round 5 — Phase 2

**Stage 0 (scouting) was done first and is reported in `STAGE0.md`.**  Its
finding: Mathlib has *no* existence theorem for Eulerian circuits, directed or
undirected (`Mathlib/Combinatorics/SimpleGraph/Trails.lean` has only necessary
conditions and lists the converse as an explicit TODO), no BEST theorem, no
matrix–tree theorem, and `Mathlib/Combinatorics/Digraph/Basic.lean` has no
walks, degrees or connectivity at all.  Architecture 2B was therefore
foreclosed and **2A (the explicit closed-form word) was chosen**.

**Stage 1 (reusable infrastructure).**  Three new results, all general in `n`:

- `realizes_I` … `realizes_VI`: each of the six form pairs realizes its class
  outright.  Unlike `realizes_iff_form` these need *no* bound on `k`, since
  they only exhibit the translate; they are what the parametric verification
  uses.
- `isIntervalCycle_of_classMap`: if every window of `D` realizes the class
  `K i` and `K : ZMod (n-3) → ℕ` is injective into `Finset.Icc 2 (n-2)`, then
  `D` is an interval cycle.  (Injective + equal cardinalities ⇒ bijective;
  uniqueness is `realizes_class_unique`.)
- `stepsOf_partialSum` and `exists_zigzag_of_word`: the **word-to-cycle
  bridge**.  From an integer word `W : ℕ → ℤ` of length `n - 3` that closes up
  mod `n`, wraps (`W (n-3) = W 0`), has an injective class assignment `K`
  realized windowwise, and opens with the chromatic zigzag `W 0 = 2`,
  `K 0 = 2`, one gets `∃ c, IsCycle n c ∧ IsZigzag n (stepsOf n c)` — the
  pitch cycle being the partial sums of `W`.

**Stage 2A (the two chains).**  The PHASE2.md words were transcribed, not
re-derived:

- odd chain, `n = 15 + 6t`: `wOdd`, `blkOdd`, `sufOdd`, classes `kOdd`,
  `kBlkOdd`, `kSufOdd`;
- even chain, `n = 18 + 6t`: `wEven`, `tlEven`, `sufEven`, classes `kEven`,
  `kTlEven`, `kSufEven`.

Each word is defined on `ℕ` by position, piecewise over the regions
prefix / blocks (or tails) / cap / suffix, with the block index recovered as
`(i-3)/6` and the offset as `(i-3)%6` (so all the position arithmetic stays in
`ℕ`, where `omega` lives).  For each chain there are four facts:

| fact | odd | even |
|---|---|---|
| region decomposition | `region_odd` | `region_even` |
| classes lie in `[2, n-2]` | `kOdd_mem` | `kEven_mem` |
| class map injective | `kOdd_inj` | `kEven_inj` |
| every window realizes its class | `real_odd` | `real_even` |
| integer sum (closure) | `wOdd_total` (`= 0`) | `wEven_total` (`= n`) |

`real_odd` / `real_even` are the substance: eighteen resp. twenty-one window
cases, each identifying the form (I…VI) and discharging two `ZMod n`
identities.  Every one of those identities is either a ring identity or
follows from `(n : ZMod n) = 0` with coefficient `±1`; the small local tactic
`modclose` does exactly that.  The form pattern is completely regular —
prefix `II, III, IV`, each block/tail `VI, III, V, I, II, IV`, odd cap `VI`,
odd suffix `III, V, I, II, V, I, II, IV`, even suffix `(II, V, I)` four times.

`exists_zigzag_odd_chain` and `exists_zigzag_even_chain` feed the four facts
into `exists_zigzag_of_word`; `exists_zigzag_of_three_dvd` splits `n` by
`n % 6` (with `n = 9` handled by the existing witness) and closes the
existence direction of `zigzag_classification`.

**On the Stage-2A milestone gate.**  PHASE2.md asks for kernel-`decide`
checks of the `t = 1` instances (`n = 21`, `n = 24`) as a transcription
guard *before* the parametric proof.  The parametric proof went through
directly and subsumes the gate: `exists_zigzag_odd_chain 1` and
`exists_zigzag_even_chain 1` *are* the `n = 21` and `n = 24` statements, and
they are now theorems rather than `decide` checks, so no separate certificate
was added.  (Transcription of the formulas was checked before formalizing by
re-running the supplied `make_words.py`, which reports `OK zigzag` at twelve
instances.)

**Definition changes to report.**  No existing definition or statement was
changed.  Two conventions inside the *new* definitions are worth flagging:
`sufOdd 8` and `sufEven 12` — one past the last real entry — are set to `2`,
the first entry of the word, so that the cyclic wrap `W (n-3) = W 0` needed by
`exists_zigzag_of_word` holds definitionally and no modular index arithmetic
is needed anywhere.

**Regression check.**  All round-4 results are intact: the audit below is
identical to the round-4 audit on every previously listed name, and
`no_bad_plan_12`/`twelve_no_zigzag` still carry exactly the accepted
`native_decide` axioms.  `maxHeartbeats` is `400000` at all twelve
`set_option` sites and is never raised.  No new linter warnings: the same four
`unused variable` warnings as in round 4, and no others.  `Mzp.lean` is now
2587 lines; it was kept as a single file, as the commission specifies.

## Status by commissioned tag

| tag | statement name | status | note |
|---|---|---|---|
| SORRY-1 | `drift_stepsOf` | CLOSED | |
| SORRY-2 | `realizes_iff_form` | CLOSED | Reverse direction rewritten (see "Heartbeats"). |
| SORRY-3 | `adjacent_semitones` | CLOSED (new in round 3) | Six-form case analysis on `ZMod.val`. |
| SORRY-4 | `form_contribution` | CLOSED | |
| SORRY-5 | `chromatic_contribution` | CLOSED | |
| SORRY-6 | `telescope` | CLOSED | |
| SORRY-7 | `fee_sum` | CLOSED | |
| SORRY-8a | `realizes_class_unique` | CLOSED | |
| SORRY-8b | `exists_class_at` | CLOSED (genuinely proved in round 4) | |
| SORRY-8c | `zigzag_three_dvd`, `cycle_zigzag_three_dvd` | CLOSED | |
| SORRY-9a | `badPlan_iff` | CLOSED | |
| SORRY-9 | `no_bad_plan_12` | CLOSED | Statement unchanged; enumeration re-encoded (patches A/B plus a six-way split). |
| SORRY-10 | `cycle_gives_bad_plan` | CLOSED (new in round 3) | Position↔class bijection, multiset reindexing, drift zero, chromatic index. |
| SORRY-11 | `six_no_cycle` | CLOSED | Now proved by **kernel `decide`** (no `native_decide`), as the commission preferred. |
| SORRY-12 | `exists_zigzag_nine` | CLOSED | kernel `decide`. |
| SORRY-13 | `exists_zigzag_fifteen` | CLOSED | kernel `decide`. |
| SORRY-14 | `exists_zigzag_eighteen` | CLOSED | kernel `decide`. |
| SORRY-15 | `zigzag_classification` | CLOSED (round 5) | Forward direction from `cycle_zigzag_three_dvd` + `twelve_no_zigzag`; existence from `exists_zigzag_of_three_dvd` (the n = 9 witness and the two closed-form chains). |

## Round-4 repair — `IsIntervalCycle` restored to the commissioned form

Round 3 shipped `IsIntervalCycle` with a second conjunct

```
(∀ i, ∃ k ∈ Finset.Icc 2 (n - 2), RealizesClass n k (D i) (D (i + 1)))
```

which was **not** part of the commissioned definition; it was the content
of SORRY-8b. Assuming it strengthened the hypothesis and therefore
weakened every negative result. This was not reported at the time; it has
now been repaired.

- The definition is back to the single conjunct

  ```
  def IsIntervalCycle (D : ZMod (n - 3) → ZMod n) : Prop :=
    ∀ k ∈ Finset.Icc 2 (n - 2), ∃! i : ZMod (n - 3),
      RealizesClass n k (D i) (D (i + 1))
  ```

- `exists_class_at` (SORRY-8b) is now **proved** by the supplied
  pigeonhole argument: the class → position map `P` is injective by
  `realizes_class_unique`; if position `i` realized no class, `P` would
  map the `n - 3` classes of `Finset.Icc 2 (n - 2)` into
  `Finset.univ.erase i`, of cardinality `n - 4`. Only one syntactic
  repair to the supplied body was needed: in this Mathlib,
  `Finset.card_le_card_of_injOn` takes a `Set.MapsTo` and a `Set.InjOn`,
  so the two hypotheses are passed through `Finset.mem_coe` with the
  finsets `s := S`, `t := Finset.univ.erase i` given explicitly. The
  mathematical argument is unchanged.

- Consequent adjustments elsewhere: `hD.1 k hk` → `hD k hk` in
  `zigzag_three_dvd` and in `cycle_gives_bad_plan` (four occurrences),
  and `hD.2 i` → `exists_class_at n hn D hD i` in `adjacent_semitones`.
  The `decide` proofs of `six_no_cycle`, `exists_zigzag_nine`,
  `exists_zigzag_fifteen`, `exists_zigzag_eighteen` were unaffected
  (they now check one conjunct fewer).

- Ordering: because `adjacent_semitones` (§1) consumes `exists_class_at`,
  the pair `realizes_class_unique` / `exists_class_at` (SORRY-8a, 8b) was
  moved from §2 up into §1, immediately before `adjacent_semitones`. No
  statement was changed by the move.

- Rebuilt (`lake build`, 8027 jobs, `Mzp` elaboration ≈ 2129 s) and the
  raw `#print axioms` output below was re-collected; it is **unchanged**
  from round 3. The `hn` hypothesis of `exists_class_at` is now used, so
  the unused-variable warnings drop from five to four.

## Round-3 patches

**Patch A (enumeration).** Applied as specified: `tabulate_eq` was added
and `no_bad_plan_12` now reasons about `![F 0, …, F 8]` instead of
quantifying over the function type `Fin 9 → Fin 6`. The statement is
unchanged. This alone cut the full-file elaboration from ≈ 5500 s to
≈ 1700 s.

**Patch B (conjunct order).** Applied verbatim: `badPlanCheck` now tests
the chromatic-index disjunction first, then the drift sum, then the
twelve-pass balance count. `badPlan_iff` needed only the predicted
conjunct reshuffle (`tauto` after the `form_multiset_eq_iff_counts`
rewrite).

**Additional re-encoding (needed).** With patches A and B in place the
single `native_decide` over nine nested `Fin 6` quantifiers still
exceeded 400000 heartbeats inside `Mzp.lean` (it fitted, barely, in an
isolated test file). Rather than raise the ceiling, the enumeration was
**split by the value of `F 0`** into six independent slices
`no_bad_head_0 … no_bad_head_5`, each quantifying over eight nested
`Fin 6`s, each with its own `set_option maxHeartbeats 400000 in`.
`no_bad_plan_12` cases on `F 0` and applies the matching slice. The
statement of `no_bad_plan_12` is unchanged; every slice elaborates
inside the standing budget.

## Heartbeats

- No `set_option maxHeartbeats 0` remains, and no budget above 400000 is
  used anywhere in the file. `grep -n maxHeartbeats Mzp.lean` shows only
  `400000`.
- The two former `2000000` wrappers were reduced to `400000`. One of
  them, before `realizes_iff_form`, then **failed** at 400000: the six
  reverse-direction cases were closed by `simp; ring_nf; ext; aesop`.
  Instead of raising the limit, those six cases were rewritten as
  explicit `Finset` triple-permutation rewrites (three local
  `insert`-commutation facts plus `ring` normalisations of the
  translates). `realizes_iff_form` now elaborates well inside 400000.
  The other wrapper (`form_multiset_eq_iff_counts`) is fine at 400000.
- No declaration needed to be isolated with a budget-failure `sorry`.

## Raw axiom audit

Produced with `lake env lean Audit.lean` (the file `Audit.lean` in the
project root; it is not part of the default build target) against the
`Mzp.olean` from the successful build:

```
'MZP.drift_stepsOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.realizes_iff_form' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.adjacent_semitones' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.form_contribution' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.chromatic_contribution' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.telescope' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.fee_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.realizes_class_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.exists_class_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.zigzag_three_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.cycle_zigzag_three_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.badPlan_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.no_bad_plan_12' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'MZP.cycle_gives_bad_plan' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.twelve_no_zigzag' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
'MZP.six_no_cycle' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.exists_zigzag_nine' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.exists_zigzag_fifteen' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.exists_zigzag_eighteen' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.isIntervalCycle_of_classMap' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.stepsOf_partialSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.exists_zigzag_of_word' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.real_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.kOdd_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.wOdd_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.real_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.kEven_inj' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.wEven_total' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.exists_zigzag_odd_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.exists_zigzag_even_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.exists_zigzag_of_three_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'MZP.zigzag_classification' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
```

Reading of the audit:

- Everything except the two entries below is closed with the standard
  axioms only.
- `no_bad_plan_12` and hence `twelve_no_zigzag` carry
  `Lean.ofReduceBool` / `Lean.trustCompiler`: that is the accepted
  `native_decide` certificate for the 6^9 twelve-tone enumeration.
- `six_no_cycle` no longer carries `Lean.ofReduceBool`: it is now a
  kernel `decide` (with `maxRecDepth 4000`).
- `zigzag_classification` no longer carries `sorryAx`.  It carries
  `Lean.ofReduceBool` / `Lean.trustCompiler` only because its forward
  direction goes through `twelve_no_zigzag`.
- Every Phase-2 declaration (`isIntervalCycle_of_classMap`,
  `stepsOf_partialSum`, `exists_zigzag_of_word`, `real_odd`, `real_even`,
  `kOdd_inj`, `kEven_inj`, `wOdd_total`, `wEven_total`, the two chain
  theorems and `exists_zigzag_of_three_dvd`) depends on the standard axioms
  only.

## New mathematics closed in round 3

- **SORRY-10, `cycle_gives_bad_plan`.** For a zigzag interval cycle at
  n = 12: the chosen realizing position for class `k = i + 2` gives a
  map `q : Fin 9 → ZMod 9` which is injective by
  `realizes_class_unique`, hence bijective by cardinality; the form
  index `F i` comes from `realizes_iff_form`. Balance is the two
  reindexings `multiset_map_univ_equiv` (along `q`) and
  `multiset_map_univ_shift` (along `+1`); drift zero is
  `drift_stepsOf`; and the class-2 index lies in `{1,2,3,4}` because
  indices 0 and 5 are exactly the scalar shapes `(1,1)` and `(-1,-1)`,
  which the zigzag hypothesis forbids. Three reusable helper lemmas
  (`multiset_map_univ_equiv`, `multiset_map_univ_shift`,
  `exists_form_index`) were added.
- **SORRY-3, `adjacent_semitones`.** With `exists_class_at` producing a class `k`
  at the window, `realizes_iff_form` gives six shapes; comparing
  `ZMod.val`s of the components (all of `1, n-1, k, k-1, n-k, n+1-k`
  lie below `n`) rules out every mixed-sign pair by `omega`, so the two
  semitone steps agree; the surviving shapes are the class-2 forms I and
  VI, which give `ChromaticAt` directly.
- **SORRY-15, forward direction.** `3 ∣ n` is `cycle_zigzag_three_dvd`;
  `n ≠ 12` is `twelve_no_zigzag` after substituting `n = 12`.

## What remains

Nothing: `Mzp.lean` is sorry-free.  The paper's numerical census claims
remain out of scope, as the commission specifies.

## Remaining linter warnings

Four `unused variable` warnings survive (round 4; `exists_class_at`'s
`hn` is now used), all of them hypotheses of
**supplied** statements that turned out not to be needed by the proofs:
`hn` in `w_one`, `hkn` in `contribution_arith_IV` and
`contribution_arith_V`, and `hn` in `telescope`. The hypotheses were left in place rather than
silently changing commissioned signatures. All other linter warnings
were fixed at the source (an unused simp argument in `six_no_cycle`, an
unreachable tactic in `fee_sum`, and an unused hypothesis of the
internal helper `contribution_sum_by_class`).

## Toolchain

- `lean-toolchain`: `leanprover/lean4:v4.28.0`
- Mathlib checkout used: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
- Lake still warns that the manifest records Mathlib as a path
  dependency while `lakefile.toml` records a Git dependency; this is
  harmless for the build.
