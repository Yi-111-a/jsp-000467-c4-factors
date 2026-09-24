import JSP467.Defs
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

/-!
# JSP-000467 — spanning C4-factors via minimum degree (Wang 2010 / Erdős–Faudree)

Catalog: What minimum degree forces a spanning collection of vertex-disjoint four-cycles?
Publication: Wang, Graphs Combin. 26 (2010) 833–877 —
Proof of the Erdős–Faudree Conjecture on Quadrilaterals.

**Statement (Wa10).** Let `G` be a (simple, finite) graph on `4k` vertices with
minimum degree `δ(G) ≥ 2k`. Then `G` contains `k` vertex-disjoint quadrilaterals
(copies of `C₄`), i.e. a spanning `C₄`-factor.

The bound is sharp: the complete bipartite graph `K_{2k-1, 2k+1}` has `4k`
vertices and minimum degree `2k - 1`, yet every `C₄` uses two vertices from each
side, so it contains at most `k - 1` disjoint quadrilaterals.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-! ## The Erdős–Faudree conjecture, proved by Wang (2010) -/

/-- **Wang (Wa10).** Every finite simple graph on `4k` vertices with minimum
degree at least `2k` contains `k` vertex-disjoint quadrilaterals covering all
vertices. -/
theorem spanning_c4_factors_min_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k)
    (hcard : Fintype.card V = 4 * k)
    (hmin : 2 * k ≤ G.minDegree) :
    G.HasQuadFactor := by
  sorry

end SimpleGraph
