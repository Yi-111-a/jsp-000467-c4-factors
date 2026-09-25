import JSP467.Main
import JSP467.Chord
import JSP467.WDefs

/-!
# JSP-000467 — cover decompositions (edge-maximal route)

A *cover* of `G` is a quadrilateral packing `S` together with a leftover
4-element set `U` covering every vertex.  In an edge-maximal counterexample to
the Erdős–Faudree theorem every non-edge `u - v` produces such a cover with
`u, v ∈ U` non-adjacent (the `C₄` through the added edge, minus that edge, is a
`P₄`).  This is the replacement for the RSW99 precursor and for the packing
enlargement route.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- A *cover* of `G`: a quadrilateral packing `S` and a leftover 4-element set
`U` disjoint from `S` such that `S ∪ U` covers every vertex. -/
structure IsCover (S : Finset (Finset V)) (U : Finset V) : Prop where
  hS : G.IsQuadPacking S
  hcard : U.card = 4
  hdisj : Disjoint (S.biUnion id) U
  hcover : S.biUnion id ∪ U = Finset.univ

variable {G}

/-- The packing part of a cover on `4 k` vertices has `k - 1` blocks. -/
theorem IsCover.card_quads {S : Finset (Finset V)} {U : Finset V}
    (hc : G.IsCover S U) {k : ℕ} (hcard : Fintype.card V = 4 * k) :
    S.card + 1 = k := by
  have hdisj : (S : Set (Finset V)).PairwiseDisjoint id :=
    fun B hB C hC hne => hc.hS.2 B hB C hC hne
  have hScard : (S.biUnion id).card = 4 * S.card := by
    calc (S.biUnion id).card
        = ∑ B ∈ S, (id B).card := Finset.card_biUnion hdisj
      _ = ∑ _B ∈ S, 4 := Finset.sum_congr rfl fun B hB => (hc.hS.1 B hB).1
      _ = 4 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hunion : S.biUnion id ∪ U = Finset.univ := hc.hcover
  have hcardU : (S.biUnion id ∪ U).card = Fintype.card V := by
    rw [hunion, Finset.card_univ]
  rw [Finset.card_union_of_disjoint hc.hdisj, hScard, hc.hcard, hcard] at hcardU
  omega

/-- If the leftover of a cover is itself a quadrilateral block, the graph has a
spanning quadrilateral factor. -/
theorem IsCover.factor_of_quad_left {S : Finset (Finset V)} {U : Finset V}
    (hc : G.IsCover S U) (hU : G.IsQuadBlock U) : G.HasQuadFactor := by
  refine HasQuadFactor.insert_block hU ?_ hc.hS.1 hc.hS.2 ?_
  · rw [Finset.union_comm]
    exact hc.hcover
  · exact fun t ht => hc.hdisj.symm.mono_right (Finset.subset_biUnion_of_mem id ht)

end SimpleGraph
