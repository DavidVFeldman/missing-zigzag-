# Phase 2, Stage 0 — scouting report on Mathlib's directed-Eulerian support

Mathlib revision inspected: the checkout in `.lake/packages/mathlib`
(`v4.28.0` tag, rev `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
Method: exhaustive `rg` over `Mathlib/` for `eulerian`, `Eulerian`,
`BEST theorem`, `arborescence`, `matrix.tree`, `Kirchhoff`, plus a read
of every file that matched and of `Mathlib/Combinatorics/Digraph/`.

## (a) Existence of an Eulerian circuit for a directed multigraph

**No.** Mathlib has no existence theorem for Eulerian circuits, in the
directed case *or* the undirected case.

Everything Mathlib knows about Eulerian objects lives in one file,
`Mathlib/Combinatorics/SimpleGraph/Trails.lean`, and it is entirely
about `SimpleGraph` (undirected, loopless, **no parallel edges**):

* `SimpleGraph.Walk.IsEulerian (p : G.Walk u v) : Prop :=
   ∀ e, e ∈ G.edgeSet → p.edges.count e = 1`
* `SimpleGraph.Walk.IsEulerian.isTrail`
* `SimpleGraph.Walk.isEulerian_iff`, `IsTrail.isEulerian_iff`,
  `IsEulerian.edgeSet_eq`, `IsEulerian.edgesFinset_eq`
* `SimpleGraph.Walk.IsTrail.even_countP_edges_iff`
* `SimpleGraph.Walk.IsEulerian.even_degree_iff`
* `SimpleGraph.Walk.IsEulerian.card_filter_odd_degree`,
  `IsEulerian.card_odd_degree`

Every one of these is a *necessary* condition extracted **from a given**
Eulerian trail. The converse is an explicit open TODO in the file's own
module docstring:

> ## TODO
> * Prove that there exists an Eulerian trail when the conclusion to
>   `SimpleGraph.Walk.IsEulerian.card_odd_degree` holds.

The only other occurrences of the word in Mathlib are the *concrete*
construction `SimpleGraph.cycleGraph_EulerianCircuit (n : ℕ) :
(cycleGraph (n + 3)).Walk 0 0` in
`Mathlib/Combinatorics/SimpleGraph/Circulant.lean` (a hand-built walk
around a cycle graph, used for graph colourings), which is of no use
here.

What data would a directed version want? There is essentially nothing to
plug into. `Mathlib/Combinatorics/Digraph/Basic.lean` (237 lines) defines
`structure Digraph (V) where Adj : V → V → Prop` and then *only* the
complete lattice/Boolean-algebra structure on `Digraph V`
(`sup_adj`, `inf_adj`, `sdiff_adj`, `sSup_adj`, …). There is **no**
`Digraph.Walk`, no `Digraph.Path`, no in-/out-degree, no connectivity.
`Mathlib/Combinatorics/Digraph/Orientation.lean` only relates a digraph
to its underlying simple graph. `Quiver` has `Quiver.Path` and
`Mathlib/Combinatorics/Quiver/Arborescence.lean`, but the latter is only
`root`, `arborescenceMk`, `shortestPath`, `geodesicSubtree` — no
counting, no Eulerian theory, and no finiteness API.

So encoding our multigraph would not be "encoding into an existing
theorem": it would mean **building directed-multigraph walk theory and
proving Euler's theorem from scratch** (choose a data model with
parallel edges, define directed trails, in/out degree, weak/strong
connectivity, then Hierholzer). That is a project on its own scale
comparable to the whole of Phase 1.

## (b) BEST theorem / directed Eulerian counting

**No.** No occurrence of the BEST theorem, of Eulerian circuit counting,
of spanning arborescence counting, or of the matrix–tree theorem
(searches for `BEST theorem`, `arborescence`, `matrix.tree`, `Kirchhoff`
return nothing beyond the four `Arborescence.lean` definitions above).
Mathlib has no directed Eulerian counting of any kind.

## (c) Recommendation

**Architecture 2A — the explicit closed-form word.** Route 2B is
foreclosed: it bottoms out in "balanced + connected ⇒ Eulerian circuit
exists" for a directed multigraph, and that theorem does not exist in
Mathlib in any form, nor does the infrastructure (directed walks,
degrees, connectivity for multigraphs) one would need to state it. Route
2B would therefore cost the Hierholzer development *plus* the encoding
of our class/edge multigraph into it, *plus* the paper's §8 connectivity
argument — with the graph-theoretic development being pure overhead that
the final statement never mentions.

Route 2A needs no graph theory at all: the words of PHASE2.md §2 are
already machine-verified at twelve instances, the target statement
`IsIntervalCycle` is a `∃!`-per-class statement that reduces to
(i) a class-assignment function `K` that is a bijection onto
`Finset.Icc 2 (n-2)`, (ii) `RealizesClass n (K i) (D i) (D (i+1))` for
every window, and (iii) uniqueness, which is already available from the
Phase-1 lemma `realizes_class_unique` together with injectivity of `K`.
All three are arithmetic in `ℕ`/`ZMod n`, i.e. `omega`/`decide`-shaped
work, which is where the existing file's machinery already lives.

Proceeding with 2A.
