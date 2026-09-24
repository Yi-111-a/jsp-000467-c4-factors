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

## Structure of the formalization

The headline theorem `spanning_c4_factors_min_degree` is reduced to a single
open step, `exists_larger_quadPacking`: any quadrilateral packing that does not
cover the whole vertex set can be enlarged.  Everything else — the notion of
packing (`IsQuadPacking`), existence of a maximum-cardinality packing
(`exists_max_card_quadPacking`), and the final maximality contradiction — is
proved in full here.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-! ## Quadrilateral packings -/

/-- A family of pairwise-disjoint quadrilateral blocks of `G` (not necessarily
covering all vertices). -/
def IsQuadPacking (S : Finset (Finset V)) : Prop :=
  (∀ s ∈ S, G.IsQuadBlock s) ∧ ∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s t

variable {G}

omit [Fintype V] [DecidableEq V] in
/-- The empty family is a quadrilateral packing. -/
theorem IsQuadPacking.empty : G.IsQuadPacking ∅ :=
  ⟨fun s hs => absurd hs (Finset.notMem_empty s),
   fun s hs _ _ _ => absurd hs (Finset.notMem_empty s)⟩

omit [DecidableEq V] in
/-- Finiteness of the vertex set implies that a maximum-cardinality
quadrilateral packing exists: the packings form a nonempty subfamily of the
finite family of all `Finset (Finset V)`. -/
theorem exists_max_card_quadPacking :
    ∃ S : Finset (Finset V), G.IsQuadPacking S ∧
      ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card ≤ S.card := by
  classical
  set P : Finset (Finset (Finset V)) :=
    univ.filter fun S => G.IsQuadPacking S with hPdef
  have hmem : ∀ S : Finset (Finset V), S ∈ P ↔ G.IsQuadPacking S := by
    intro S
    simp [hPdef]
  have hne : P.Nonempty := ⟨∅, (hmem ∅).2 IsQuadPacking.empty⟩
  obtain ⟨S, hSP, hSmax⟩ := Finset.exists_max_image P Finset.card hne
  exact ⟨S, (hmem S).1 hSP, fun T hT => hSmax T ((hmem T).2 hT)⟩

/-- A quadrilateral packing covering every vertex is a spanning quadrilateral
factor. -/
theorem HasQuadFactor.of_quadPacking {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S) (hcov : S.biUnion id = Finset.univ) :
    G.HasQuadFactor :=
  ⟨S, hS.1, hS.2, hcov⟩

/-! ## The Erdős–Faudree conjecture, proved by Wang (2010) -/

/-- **Core gap (Wang, Wa10).** Under the minimum-degree hypothesis
`δ(G) ≥ 2k` on `4k` vertices, every quadrilateral packing that fails to cover
all vertices can be enlarged to a strictly larger one.

This single open step is the mathematical heart of the Erdős–Faudree
conjecture: Wang's 45-page argument shows that a non-covering packing can
always be extended to a larger one (via switching arguments on almost-covering
configurations, bipartite-hole constructions, and extensive case analysis). -/
theorem exists_larger_quadPacking (k : ℕ) [DecidableRel G.Adj] (hk : 1 ≤ k)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hncov : S.biUnion id ≠ Finset.univ) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  sorry

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
