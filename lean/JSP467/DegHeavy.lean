import JSP467.CaseB
import JSP467.Exchange
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# JSP-000467 — low leftover-degree forces a heavy block

The "low leftover-degree ⟹ heavy" step of Wang's enlargement argument.  For a
quadrilateral packing `S` of cardinality `m < k` in a `4k`-vertex graph with
minimum degree at least `2k`, an uncovered vertex `v` whose leftover-degree
(the number of its neighbours inside the uncovered set `U`) is at most
`2 * (k - m) - 2` must have at least `2m + 2` neighbours inside the covered
set `⋃ S`.  Pigeonhole over the `m` disjoint four-vertex blocks then forces
some block `B ∈ S` containing at least three neighbours of `v`
(`exists_heavy_block`).

Since the argument only uses the cardinality and the packing property of `S`,
the same conclusion holds verbatim for any exchanged packing `S'` with
`S'.card = S.card`; this is recorded as
`exists_heavy_block_of_low_leftover_degree_exchanged`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Low leftover-degree forces a heavy block.**  If `v` is uncovered and has
at most `2 * (k - S.card) - 2` neighbours among the uncovered vertices, then
its `≥ 2k - (2 * (k - S.card) - 2) = 2 * S.card + 2` covered neighbours
pigeonhole into some block with at least three of them. -/
theorem exists_heavy_block_of_low_leftover_degree (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hlt : S.card < k) {v : V}
    (hv : v ∈ Finset.univ \ S.biUnion id)
    (hdeg : ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset v).card
      ≤ 2 * (k - S.card) - 2) :
    ∃ B ∈ S, 3 ≤ (B ∩ G.neighborFinset v).card := by
  classical
  -- Every neighbour of `v` is either covered (in `⋃ S`) or uncovered.
  have hsub : G.neighborFinset v
      ⊆ ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset v)
        ∪ (S.biUnion id ∩ G.neighborFinset v) := by
    intro w hw
    by_cases hwB : w ∈ S.biUnion id
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_inter.2 ⟨hwB, hw⟩))
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_inter.2
        ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ w, hwB⟩, hw⟩))
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((Finset.univ \ S.biUnion id)
      ∩ G.neighborFinset v) (S.biUnion id ∩ G.neighborFinset v)
  have hdegv : 2 * k ≤ (G.neighborFinset v).card :=
    hmin.trans (G.minDegree_le_degree v)
  -- `|⋃S ∩ N v| ≥ 2k - (2 * (k - S.card) - 2) = 2 * S.card + 2 > 2 * S.card`.
  exact exists_heavy_block hS (by omega)

/-- The same conclusion for an *exchanged* packing: the argument needs only
the cardinality and the packing property, so any `S'` with
`S'.card = S.card` inherits the statement. -/
theorem exists_heavy_block_of_low_leftover_degree_exchanged (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S S' : Finset (Finset V)} (hS' : G.IsQuadPacking S')
    (hcard' : S'.card = S.card) (hlt : S.card < k) {v : V}
    (hv : v ∈ Finset.univ \ S'.biUnion id)
    (hdeg : ((Finset.univ \ S'.biUnion id) ∩ G.neighborFinset v).card
      ≤ 2 * (k - S.card) - 2) :
    ∃ B ∈ S', 3 ≤ (B ∩ G.neighborFinset v).card := by
  rw [← hcard'] at hdeg hlt
  exact exists_heavy_block_of_low_leftover_degree G k hcard hmin hS' hlt hv hdeg

end SimpleGraph
