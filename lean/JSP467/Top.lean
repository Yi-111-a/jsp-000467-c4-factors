import JSP467.Reduce

/-!
# JSP-000467 — headline theorems (Wang 2010 / Erdős–Faudree)

Catalog: What minimum degree forces a spanning collection of vertex-disjoint
four-cycles?
Publication: Wang, Graphs Combin. 26 (2010) 833–877 —
Proof of the Erdős–Faudree Conjecture on Quadrilaterals.

**Statement (Wa10).** Let `G` be a (simple, finite) graph on `4k` vertices with
minimum degree `δ(G) ≥ 2k`. Then `G` contains `k` vertex-disjoint quadrilaterals
(copies of `C₄`), i.e. a spanning `C₄`-factor.

The bound is sharp: the complete bipartite graph `K_{2k-1, 2k+1}` has `4k`
vertices and minimum degree `2k - 1`, yet every `C₄` uses two vertices from each
side, so it contains at most `k - 1` disjoint quadrilaterals.

The enlargement step `exists_larger_quadPacking` is assembled in
`JSP467.Reduce`: every non-covering packing is dominated by a
lexicographically maximal one, which is either clean (proved in
`JSP467.Clean`) or carries a heavy vertex (`wang_heavy_lex`, the residual
switching core of Wa10).
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- **Core step (Wang, Wa10).** Under the minimum-degree hypothesis
`δ(G) ≥ 2k` on `4k` vertices, every quadrilateral packing that fails to cover
all vertices can be enlarged to a strictly larger one. -/
theorem exists_larger_quadPacking (k : ℕ) [DecidableRel G.Adj] (hk : 1 ≤ k)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hncov : S.biUnion id ≠ Finset.univ) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card :=
  exists_larger_quadPacking_of_lexmax G k hk hcard hmin hS hncov

/-- **Wang (Wa10).** Every finite simple graph on `4k` vertices with minimum
degree at least `2k` contains `k` vertex-disjoint quadrilaterals covering all
vertices. -/
theorem spanning_c4_factors_min_degree
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k)
    (hcard : Fintype.card V = 4 * k)
    (hmin : 2 * k ≤ G.minDegree) :
    G.HasQuadFactor := by
  classical
  obtain ⟨S, hS, hSmax⟩ := G.exists_max_card_quadPacking
  by_cases hcov : S.biUnion id = Finset.univ
  · exact HasQuadFactor.of_quadPacking hS hcov
  · obtain ⟨T, hT, hlt⟩ :=
      G.exists_larger_quadPacking k hk hcard hmin hS hcov
    exact absurd (hSmax T hT) (not_le_of_gt hlt)

end SimpleGraph
