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

This module defines quadrilateral packings (`IsQuadPacking`) and proves
existence of a maximum-cardinality packing (`exists_max_card_quadPacking`).
The enlargement step and the headline theorem
`spanning_c4_factors_min_degree` are assembled downstream in `JSP467.Top`.
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

/-! ## Assembly downstream

The enlargement step `exists_larger_quadPacking` and the headline theorem
`spanning_c4_factors_min_degree` live in `JSP467.Top` (downstream of the
case-analysis files `Clean`/`CaseB`/`LexMax`/`Reduce`, which import this
module for `IsQuadPacking`). -/

end SimpleGraph
