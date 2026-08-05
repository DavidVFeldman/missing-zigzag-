# Computational scripts

Every enumerative claim in the paper was computed by two independent
programs using **different representations** of trichord classes: one
canonicalizing the pitch-class set under rotation, the other using the
rotation-canonical cyclic *gap word*. The second is inversion-sensitive
by construction — a sorted interval vector would silently identify a
class with its inversion, which is exactly the distinction the paper
turns on, so a checker sharing that blind spot would verify nothing.

| File | Purpose |
| --- | --- |
| `verify_examples.py` | Checks every explicit example printed in the paper directly against the definition: the 12TET cycle and its window classes, the 9TET and 15TET cycles, the fourths transform, the drift-1 spiral (108 windows), the near-row, and the twelve-tone row. |
| `census_direct.c` | Direct enumeration of pitch words with gap-word class labelling; reproduces *A*(*n*), *B*(*n*) for 8 ≤ *n* ≤ 18. Build: `gcc -O2 -o census_direct census_direct.c`. |
| `census_best.py` | Independent recount of the Eulerian counts via the BEST theorem (exact fraction-free matrix-tree determinants), used for *n* = 21, 24, 27, which lie beyond direct search. Agrees plan by plan with the circuit enumeration wherever both are available. |
| `recount_12tet.py` | Recount of the 12TET cycles, semitone strata, near-rows, the omitted-trichord census, and Marsden's all-trichord rings. |
| `make_words.py` | Generates and verifies the closed-form pumped words of the existence proof, for both residue chains; `--classes` prints the window-class assignment. |

Python 3 with no third-party dependencies; `census_direct.c` needs a C
compiler.
