import JSP467.Main
import JSP467.Chord
import JSP467.WCover

/-!
# JSP-000467 — cross-edge counting between vertex sets

The counting finish of Wang (Wa10) needs a bipartite edge count
`crossEdges G A B = ∑_{a ∈ A} |B ∩ N(a)|` together with

* `crossEdges_eq_card_filter` — the count as ordered pairs,
* `crossEdges_comm` — symmetry (ordered-pair count is direction-free),
* `sum_crossEdges_biUnion` — the count splits over a disjoint family,
* `edgeSum_add_crossEdges_sdiff` — the degree sum over `U` splits into
  internal (`edgeSum`) plus external (`crossEdges`) contributions,
* `sum_neighborFinset_card_ge` — every vertex contributes `≥ δ`,
* `exists_crossEdges_ge` — the pigeonhole: a large total cross-edge count
  over a disjoint family forces one part to carry many cross edges.

All statements are over an ambient `SimpleGraph V` with `[DecidableRel G.Adj]`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The number of `A`–`B` adjacencies, counted from the `A` side:
`crossEdges G A B = ∑_{a ∈ A} |B ∩ N(a)|`.  For disjoint `A, B` this is the
number of edges between `A` and `B`. -/
def crossEdges (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : ℕ :=
  ∑ a ∈ A, (B ∩ G.neighborFinset a).card

variable [DecidableRel G.Adj]

/-- `crossEdges G A B` counts ordered pairs `(a, b) ∈ A ×ˢ B` with `a ~ b`. -/
theorem crossEdges_eq_card_filter (A B : Finset V) :
    crossEdges G A B =
      ((A ×ˢ B).filter fun p => G.Adj p.1 p.2).card := by
  have h : ∀ x ∈ A, (B ∩ G.neighborFinset x).card
      = ∑ y ∈ B, (if G.Adj x y then 1 else 0) := by
    intro x _
    rw [← Finset.card_filter]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]
  calc crossEdges G A B
      = ∑ x ∈ A, ∑ y ∈ B, (if G.Adj x y then 1 else 0) := by
        unfold crossEdges
        exact Finset.sum_congr rfl h
    _ = ((A ×ˢ B).filter fun p => G.Adj p.1 p.2).card := by
        rw [← Finset.sum_product', Finset.card_filter]

/-- The cross-edge count is symmetric (each adjacent pair appears once on
each side). -/
theorem crossEdges_comm (A B : Finset V) :
    crossEdges G A B = crossEdges G B A := by
  rw [crossEdges_eq_card_filter, crossEdges_eq_card_filter]
  refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩
  · intro p _ q _ hpq
    exact Prod.ext (Prod.ext_iff.1 hpq).2 (Prod.ext_iff.1 hpq).1
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    refine ⟨(q.2, q.1), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hq.1.2, hq.1.1⟩, hq.2.symm⟩

/-- Cross edges from a singleton are just the neighbour count in `B`. -/
theorem crossEdges_singleton (x : V) (B : Finset V) :
    crossEdges G {x} B = (B ∩ G.neighborFinset x).card := by
  unfold crossEdges
  rw [Finset.sum_singleton]

/-- Cross edges from a two-element set split into the two neighbour
counts. -/
theorem crossEdges_pair {x y : V} (h : x ≠ y) (B : Finset V) :
    crossEdges G {x, y} B =
      (B ∩ G.neighborFinset x).card +
        (B ∩ G.neighborFinset y).card := by
  unfold crossEdges
  rw [Finset.sum_pair h]

/-- Monotonicity in the second argument. -/
theorem crossEdges_mono_right {A B B' : Finset V} (h : B ⊆ B') :
    crossEdges G A B ≤ crossEdges G A B' :=
  Finset.sum_le_sum fun a _ => Finset.card_le_card
    (Finset.inter_subset_inter_right h)

/-- The cross-edge count from a fixed set `A` splits over a pairwise-disjoint
family: `∑_{B ∈ S} crossEdges A B = crossEdges A (⋃ S)`. -/
theorem sum_crossEdges_biUnion {A : Finset V} {S : Finset (Finset V)}
    (hd : (S : Set (Finset V)).PairwiseDisjoint id) :
    ∑ B ∈ S, crossEdges G A B = crossEdges G A (S.biUnion id) := by
  unfold crossEdges
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hd' : (S : Set (Finset V)).PairwiseDisjoint
      (fun B => B ∩ G.neighborFinset a) :=
    fun s hs t ht hne => Disjoint.mono Finset.inter_subset_left
      Finset.inter_subset_left (hd hs ht hne)
  rw [← Finset.card_biUnion hd']
  congr 1
  rw [Finset.biUnion_inter]
  simp only [id_eq]

/-- Degree-sum split: for any `U`, the sum of `(G.neighborFinset u).card`
over `u ∈ U` equals the internal `edgeSum` plus the cross edges from `U` to
its complement. -/
theorem edgeSum_add_crossEdges_sdiff (U : Finset V) :
    edgeSum G U + crossEdges G U (Finset.univ \ U)
      = ∑ u ∈ U, (G.neighborFinset u).card := by
  unfold edgeSum crossEdges
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hpart : G.neighborFinset u
      = (U ∩ G.neighborFinset u) ∪
          ((Finset.univ \ U) ∩ G.neighborFinset u) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_univ, G.mem_neighborFinset, true_and]
    constructor
    · intro hx
      by_cases hU : x ∈ U
      · exact Or.inl ⟨hU, hx⟩
      · exact Or.inr ⟨hU, hx⟩
    · rintro (⟨_, hx⟩ | ⟨_, hx⟩) <;> exact hx
  have hd : Disjoint (U ∩ G.neighborFinset u)
      ((Finset.univ \ U) ∩ G.neighborFinset u) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 hx2).1).2
      (Finset.mem_inter.1 hx).1
  calc (U ∩ G.neighborFinset u).card
        + ((Finset.univ \ U) ∩ G.neighborFinset u).card
      = ((U ∩ G.neighborFinset u) ∪
          ((Finset.univ \ U) ∩ G.neighborFinset u)).card :=
        (Finset.card_union_of_disjoint hd).symm
    _ = (G.neighborFinset u).card := by rw [← hpart]

/-- The degree sum over `U` is at least `|U| * δ(G)`. -/
theorem sum_neighborFinset_card_ge (U : Finset V) :
    U.card * G.minDegree ≤ ∑ u ∈ U, (G.neighborFinset u).card := by
  calc U.card * G.minDegree
      = ∑ _u ∈ U, G.minDegree := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ u ∈ U, (G.neighborFinset u).card := by
        refine Finset.sum_le_sum fun u _ => ?_
        rw [G.card_neighborFinset_eq_degree]
        exact G.minDegree_le_degree u

/-- Pigeonhole: if `A` sends more than `|S| * (r - 1)` cross edges into the
union of a pairwise-disjoint family `S`, then some part `B ∈ S` receives at
least `r` cross edges from `A`. -/
theorem exists_crossEdges_ge {A : Finset V} {S : Finset (Finset V)}
    (hd : (S : Set (Finset V)).PairwiseDisjoint id) {r : ℕ}
    (h : S.card * (r - 1) < crossEdges G A (S.biUnion id)) :
    ∃ B ∈ S, r ≤ crossEdges G A B := by
  rw [← sum_crossEdges_biUnion (G := G) hd] at h
  by_contra hcon
  push_neg at hcon
  have hle : ∑ B ∈ S, crossEdges G A B ≤ S.card * (r - 1) :=
    calc ∑ B ∈ S, crossEdges G A B
        ≤ ∑ _B ∈ S, (r - 1) :=
          Finset.sum_le_sum fun B hB => by
            have hlt := hcon B hB
            omega
      _ = S.card * (r - 1) := by rw [Finset.sum_const, smul_eq_mul]
  omega

end SimpleGraph
