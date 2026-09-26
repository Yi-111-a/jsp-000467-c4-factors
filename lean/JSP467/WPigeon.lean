import JSP467.WNine

/-!
# JSP-000467 — the degree-counting pigeonhole: the 9-edge block

The counting finish of Wang (Wa10): in a cover `(S, U)` of a `4k`-vertex
graph with `δ(G) ≥ 2k`, the degree sum over the four-vertex leftover `U`
is at least `8k`.  At most `6` of it is internal (`edgeSum G U ≤ 6`), so
at least `8k - 6` cross edges run from `U` into the `k - 1` blocks of the
packing.  Since `8k - 6 > 8 (k - 1)`, the pigeonhole yields a block
`B ∈ S` with `9 ≤ crossEdges G U B` — Wang's 9-edge block — and a second
pigeonhole (`exists_heavy_of_nine`) then produces `u ∈ U` seeing at least
three vertices of `B`.

* `crossEdges_biUnion_eq_sdiff` — the union of the packing blocks is
  exactly `univ \ U`, so the two cross-edge counts coincide.
* `crossEdges_lower_bound` — `8 * k - c ≤ crossEdges G U (S.biUnion id)`
  from the degree-sum split `edgeSum_add_crossEdges_sdiff`.
* `exists_block_nine_edges` — the pigeonhole producing the block `B` with
  `9 ≤ crossEdges G U B`.
* `exists_triple_seer` — corollary via `exists_heavy_of_nine`: some
  `u ∈ U` has `3 ≤ (B ∩ G.neighborFinset u).card`.

All statements are over an ambient `SimpleGraph V` with
`[DecidableRel G.Adj]`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

/-- In a cover `(S, U)` the union of the packing blocks is exactly the
complement of `U`, so cross edges from `U` into `S.biUnion id` are cross
edges from `U` into `univ \ U`. -/
theorem crossEdges_biUnion_eq_sdiff {S : Finset (Finset V)} {U : Finset V}
    (hc : G.IsCover S U) :
    crossEdges G U (S.biUnion id) = crossEdges G U (Finset.univ \ U) := by
  have hsdiff : Finset.univ \ U = S.biUnion id := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hx
      have hx' : x ∈ S.biUnion id ∪ U := by
        rw [hc.hcover]; exact Finset.mem_univ x
      rcases Finset.mem_union.1 hx' with h | h
      · exact h
      · exact absurd h hx
    · intro hx hU
      exact Finset.disjoint_left.1 hc.hdisj hx hU
  rw [hsdiff]

/-- **Degree-counting bound.**  With `U.card = 4` and `δ(G) ≥ 2k` the
degree sum over `U` is at least `8k`; subtracting the internal
contribution `edgeSum G U ≤ c` leaves at least `8k - c` cross edges from
`U` into the packing blocks. -/
theorem crossEdges_lower_bound {S : Finset (Finset V)} {U : Finset V}
    (hc : G.IsCover S U) {k c : ℕ} (_hcard : Fintype.card V = 4 * k)
    (hdeg : 2 * k ≤ G.minDegree) (hint : edgeSum G U ≤ c) :
    8 * k - c ≤ crossEdges G U (S.biUnion id) := by
  have hsplit := edgeSum_add_crossEdges_sdiff (G := G) U
  have hge := sum_neighborFinset_card_ge (G := G) U
  rw [hc.hcard] at hge
  rw [← crossEdges_biUnion_eq_sdiff (G := G) hc] at hsplit
  omega

/-- **Wang's 9-edge block.**  `8k - 6 > 8(k - 1) = |S| * (9 - 1)`, so
some block of the packing receives at least nine cross edges from `U`. -/
theorem exists_block_nine_edges {S : Finset (Finset V)} {U : Finset V}
    (hc : G.IsCover S U) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hk : 2 ≤ k) (hdeg : 2 * k ≤ G.minDegree) (hint : edgeSum G U ≤ 6) :
    ∃ B ∈ S, 9 ≤ crossEdges G U B := by
  have hScard : S.card + 1 = k := hc.card_quads hcard
  have hlb : 8 * k - 6 ≤ crossEdges G U (S.biUnion id) :=
    crossEdges_lower_bound hc hcard hdeg hint
  have hdisj : (S : Set (Finset V)).PairwiseDisjoint id :=
    fun B hB C hC hne => hc.hS.2 B hB C hC hne
  refine exists_crossEdges_ge hdisj (r := 9) ?_
  show S.card * 8 < crossEdges G U (S.biUnion id)
  omega

/-- **Corollary.**  The 9-edge block `B` contains a vertex triple seen by
some `u ∈ U`: `3 ≤ (B ∩ G.neighborFinset u).card`. -/
theorem exists_triple_seer {S : Finset (Finset V)} {U : Finset V}
    (hc : G.IsCover S U) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hk : 2 ≤ k) (hdeg : 2 * k ≤ G.minDegree) (hint : edgeSum G U ≤ 6) :
    ∃ B ∈ S, ∃ u ∈ U, 3 ≤ (B ∩ G.neighborFinset u).card := by
  obtain ⟨B, hB, h9⟩ := exists_block_nine_edges hc hcard hk hdeg hint
  obtain ⟨u, hu, h3⟩ := exists_heavy_of_nine hc.hcard h9
  exact ⟨B, hB, u, hu, h3⟩

end SimpleGraph
