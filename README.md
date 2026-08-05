# The Missing Zigzag — Lean 4 formalization

[![build](https://github.com/USERNAME/missing-zigzag/actions/workflows/build.yml/badge.svg)](https://github.com/USERNAME/missing-zigzag/actions/workflows/build.yml)

Machine-checked companion to

> D. V. Feldman, *The Missing Zigzag: Cycles of Semitone Trichords and a
> Conservation Law in Equal Temperament.*

A **trichord cycle** in *n*-tone equal temperament is a cyclic word of
*n*−3 pitch classes whose *n*−3 consecutive three-note windows realize,
exactly once each, every trichord class {0,1,*k*} (2 ≤ *k* ≤ *n*−2)
containing a semitone — classes taken up to transposition only, **not**
up to inversion. Every such cycle contains exactly one window realizing
the chromatic class {0,1,2}, presented either **scalarly** (a direct
chromatic run) or in **zigzag** (a broken contour such as 1–0–2).

In twelve-tone equal temperament the zigzag never occurs. This
development explains why, and settles the general case.

## What is proved

| Result | Statement |
| --- | --- |
| `zigzag_three_dvd` | A zigzag presentation forces 3 \| *n* — for interval cycles of **any** drift |
| `cycle_zigzag_three_dvd` | The same, for pitch cycles |
| `twelve_no_zigzag` | No trichord cycle in 12TET presents the chromatic in zigzag |
| `six_no_cycle` | 6TET admits no trichord cycle at all |
| `exists_zigzag_nine/fifteen/eighteen` | Explicit zigzag witnesses at *n* = 9, 15, 18 |
| `zigzag_classification` | Zigzag cycles exist **iff** 3 \| *n* and *n* ≠ 12 |

The development contains no unproved placeholders and declares no new
axioms.

**Axiom profile.** Every result depends only on Lean's three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) except
`no_bad_plan_12`, `twelve_no_zigzag`, `cycle_gives_bad_plan` and
`zigzag_classification`, which additionally carry `Lean.ofReduceBool`
and `Lean.trustCompiler` from one reflected finite computation — the
6⁹ enumeration of form-choice plans certifying the twelve-tone
exclusion. Run `Audit.lean` (below) to reproduce the audit, or read it
in [`docs/STATUS.md`](docs/STATUS.md).

## Design note

The primary formal object is the **step word** (interval cycle)
`D : ZMod (n-3) → ZMod n`, with windows the consecutive pairs
`(D i, D (i+1))`; pitch cycles are recovered by differencing. In this
setting the conservation law becomes a *telescoping identity*, so its
proof uses no graph theory, no Eulerian circuits and no multiset
balance. Existence is likewise proved without induction: the pumped
cycles are given by explicit closed-form words (see
[`scripts/make_words.py`](scripts/make_words.py)) and verified
parametrically. Mathlib has no directed-multigraph Eulerian existence
theorem; the survey that established this is in
[`docs/MATHLIB-EULERIAN-SURVEY.md`](docs/MATHLIB-EULERIAN-SURVEY.md).

## Building

Requires [`elan`](https://github.com/leanprover/elan). The toolchain
(`leanprover/lean4:v4.28.0`) and Mathlib revision are pinned.

```sh
lake exe cache get   # fetch prebuilt Mathlib oleans
lake build           # build the development
```

To reproduce the axiom audit after building:

```sh
lake env lean Audit.lean
```

Continuous integration rebuilds from a clean clone on every push,
rejects any unproved placeholder or new axiom, and uploads the axiom
audit as a build artifact.

## Reproducing the paper's computations

`scripts/` contains the programs behind the paper's enumerative claims.
Every count was computed twice, by programs using different
representations of trichord classes; see
[`scripts/README.md`](scripts/README.md).

## Citation

```bibtex
@software{feldman_missing_zigzag,
  author  = {Feldman, David Victor},
  title   = {The Missing Zigzag: Lean 4 formalization},
  year    = {2026},
  url     = {https://github.com/USERNAME/missing-zigzag},
  doi     = {10.5281/zenodo.XXXXXXX}
}
```

## License

Apache License 2.0 — see [`LICENSE`](LICENSE).
