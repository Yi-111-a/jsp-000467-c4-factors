import JSP467.Defs

/-!
# JSP-000467 — the pigeonhole step of Wang's argument

If `δ(G) ≥ d` and `d * (d - 1) > |V| - 1`, then every vertex lies on a
quadrilateral block: two neighbors `u w` of `v` must share a neighbor `x ≠ v`,
and `v - u - x - w - v` is a `C₄` through `v`.

The counting argument: if no quadrilateral block contains `v`, the sets
`N(u) \ {v}` for `u ∈ N(v)` are pairwise disjoint subsets of `V \ {v}`, each of
size at least `d - 1`.  Their union therefore has size at least
`|N(v)| * (d - 1) ≥ d * (d - 1) > |V| - 1`, a contradiction.
-/

open Finset

namespace SimpleGraph

/-- Pigeonhole step of the Wang argument: if `d(d-1) > |V| - 1` and
`δ(G) ≥ d`, then every vertex lies in a quadrilateral block. -/
theorem exists_isQuadBlock_self {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) {d : ℕ}
    (hd : d ≤ G.minDegree) (hbig : Fintype.card V < d * (d - 1) + 1) :
    ∃ s : Finset V, G.IsQuadBlock s ∧ v ∈ s := by
  classical
  by_contra hnone
  -- If no quadrilateral block contains `v`, the sets `N(u) \ {v}` for
  -- `u ∈ N(v)` are pairwise disjoint: a common neighbor `x` of `u` and `w`
  -- would close the 4-cycle `v - u - x - w - v`.
  have hdisj : ((G.neighborFinset v : Finset V) : Set V).PairwiseDisjoint
      (fun u => (G.neighborFinset u).erase v) := by
    intro u hu w hw huw
    rw [Finset.mem_coe] at hu hw
    refine Finset.disjoint_left.2 fun x hxu hxw => ?_
    obtain ⟨hxv, hux⟩ := Finset.mem_erase.1 hxu
    obtain ⟨-, hwx⟩ := Finset.mem_erase.1 hxw
    have hux' : G.Adj u x := (G.mem_neighborFinset x).1 hux
    have hwx' : G.Adj w x := (G.mem_neighborFinset x).1 hwx
    have hvu : G.Adj v u := (G.mem_neighborFinset u).1 hu
    have hvw : G.Adj v w := (G.mem_neighborFinset w).1 hw
    have hblock : G.IsQuadBlock {v, u, x, w} :=
      G.IsQuadBlock.of_cycle rfl hvu.ne hxv.symm hvw.ne hux'.ne huw hwx'.ne'
        hvu hux' hwx'.symm hvw.symm
    exact hnone ⟨_, hblock, Finset.mem_insert_self v _⟩
  -- The union of the `N(u) \ {v}` lies inside `V \ {v}`.
  have hsub : (G.neighborFinset v).biUnion
      (fun u => (G.neighborFinset u).erase v) ⊆ univ.erase v := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨u, -, hxu⟩ := hx
    exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hxu).1, Finset.mem_univ x⟩
  -- Hence its cardinality is at most `|V| - 1`.
  have hle : ((G.neighborFinset v).biUnion
      (fun u => (G.neighborFinset u).erase v)).card ≤ Fintype.card V - 1 := by
    have h := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at h
  rw [Finset.card_biUnion hdisj] at hle
  -- On the other hand every `N(u) \ {v}` has at least `d - 1` elements, so the
  -- sum is at least `|N(v)| * (d - 1) ≥ d * (d - 1)`.
  have hsum : d * (d - 1) ≤ ∑ u ∈ G.neighborFinset v,
      ((G.neighborFinset u).erase v).card := by
    have hN : d ≤ (G.neighborFinset v).card :=
      hd.trans (G.minDegree_le_degree v)
    calc d * (d - 1) ≤ (G.neighborFinset v).card * (d - 1) :=
          mul_le_mul' hN le_rfl
      _ = ∑ _u ∈ G.neighborFinset v, (d - 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ u ∈ G.neighborFinset v, ((G.neighborFinset u).erase v).card := by
          refine Finset.sum_le_sum fun u hu => ?_
          have hvmem : v ∈ G.neighborFinset u :=
            (G.mem_neighborFinset v).2 ((G.mem_neighborFinset u).1 hu).symm
          rw [Finset.card_erase_of_mem hvmem]
          have hdu : d ≤ (G.neighborFinset u).card :=
            hd.trans (G.minDegree_le_degree u)
          omega
  -- So `d * (d - 1) ≤ |V| - 1`, contradicting `|V| < d * (d - 1) + 1`.
  have hcontra : d * (d - 1) ≤ Fintype.card V - 1 := hsum.trans hle
  omega

end SimpleGraph
