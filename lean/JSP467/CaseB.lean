import JSP467.Clean
import JSP467.Exchange
import JSP467.Rotate
import JSP467.Pairing

/-!
# JSP-000467 — case split for the packing-enlargement step

Assembly of the case split for `exists_larger_quadPacking` (Wang, Wa10): a
non-covering quadrilateral packing is either *clean* — every uncovered vertex
has at most two neighbours inside every block — or exhibits a *heavy* vertex —
some uncovered `u` with at least three neighbours inside some block `B ∈ S`.

* `clean_or_exists_heavy` — the dichotomy itself (pure logic).
* `exists_larger_quadPacking_of_heavy_step` — the enlargement theorem reduced
  to a single hypothesis covering the heavy case.
* `exists_larger_quadPacking_of_leftover` — the "leftover block" exit: a
  quadrilateral block inside the uncovered set enlarges the packing.
* `exists_heavy_block` — pigeonhole: more than `2 · S.card` covered
  neighbours force a heavy block.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Trichotomy-free case split: either the packing is "clean" (every uncovered
vertex has ≤2 neighbours in every block) or some uncovered vertex is "heavy"
(≥3 neighbours in some block). -/
theorem clean_or_exists_heavy (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset (Finset V)} :
    (∀ u : V, u ∉ S.biUnion id → ∀ B ∈ S, (B ∩ G.neighborFinset u).card ≤ 2) ∨
    (∃ u : V, u ∉ S.biUnion id ∧ ∃ B ∈ S, 3 ≤ (B ∩ G.neighborFinset u).card) := by
  classical
  by_cases h : ∀ u : V, u ∉ S.biUnion id →
      ∀ B ∈ S, (B ∩ G.neighborFinset u).card ≤ 2
  · exact Or.inl h
  · refine Or.inr ?_
    push Not at h
    obtain ⟨u, hu, B, hB, hcard⟩ := h
    exact ⟨u, hu, B, hB, by omega⟩

/-- The full enlargement theorem reduced to the heavy case.  If EVERY
non-covering packing exhibiting a heavy vertex can be enlarged, then every
non-covering packing can be enlarged. -/
theorem exists_larger_quadPacking_of_heavy_step
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    (hheavy : ∀ {S : Finset (Finset V)}, G.IsQuadPacking S →
      S.biUnion id ≠ Finset.univ →
      (∃ u : V, u ∉ S.biUnion id ∧ ∃ B ∈ S, 3 ≤ (B ∩ G.neighborFinset u).card) →
      ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hncov : S.biUnion id ≠ Finset.univ) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  rcases clean_or_exists_heavy G (S := S) with hclean | hhv
  · exact exists_larger_quadPacking_of_clean G k hk hcard hmin hS hncov hclean
  · exact hheavy hS hncov hhv

/-- If the uncovered set itself contains a quadrilateral block, enlarge. -/
theorem exists_larger_quadPacking_of_leftover {G : SimpleGraph V}
    [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    {Q : Finset V} (hQ : G.IsQuadBlock Q)
    (hQU : Q ⊆ Finset.univ \ S.biUnion id) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card :=
  exists_larger_of_leftover_block hS hQ hQU

/-- If `u` is uncovered and has more than `2·S.card` neighbours among covered
vertices, some block contains ≥3 of its neighbours. -/
theorem exists_heavy_block {G : SimpleGraph V} [DecidableRel G.Adj]
    {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S) {u : V}
    (h : 2 * S.card < ((S.biUnion id) ∩ G.neighborFinset u).card) :
    ∃ B ∈ S, 3 ≤ (B ∩ G.neighborFinset u).card := by
  apply exists_block_ge_degree hS.2 (r := 3)
  omega

end SimpleGraph
