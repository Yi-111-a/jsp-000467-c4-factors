import JSP467.LexMax
import JSP467.RotApp
import JSP467.CaseB

/-!
# JSP-000467 — the single lex-max heavy-exchange step

The iteration fuel for Wang's switching argument (Wa10): under a
*lexicographically maximal* quadrilateral packing `S` (maximal `blockSum`
first, maximal leftover `edgeSum` second), an uncovered vertex `u` with ≥ 3
neighbours inside a block `B ∈ S` can be exchanged for some `w ∈ B`, yielding
a packing `S'` of the same cardinality whose leftover is
`(univ \ ∪S).erase u ∪ {w}` and which is *strictly better* in the lex order —
either `blockSum` drops, or it stays equal and the freed vertex `w` sees no
more of the reduced leftover than `u` did.

* `lexmax_heavy_exchange` — the packaged disjunctive exchange step.
* `exists_larger_of_exchange_leftover_quad` — the exit: a quadrilateral
  block inside the post-exchange leftover enlarges the packing.
* `exists_larger_of_new_leftover_block` — glue: given any same-cardinality
  packing `S'` and a quad block in its leftover, `S` enlarges.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **Lex-max heavy exchange.**  For a lexicographically maximal packing `S`
and an uncovered `u` heavy on the block `B` (≥ 3 neighbours), some `w ∈ B`
can be swapped for `u`.  The exchanged packing `S'` has the same cardinality,
leftover `(univ \ ∪S).erase u ∪ {w}`, and is strictly below `S` in the lex
order: either `blockSum S' < blockSum S`, or `blockSum` is preserved and the
rotation bound on `w`'s reduced-leftover neighbourhood holds. -/
theorem lexmax_heavy_exchange (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    {u : V} (hu : u ∈ Finset.univ \ S.biUnion id) {B : Finset V} (hB : B ∈ S)
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    ∃ w ∈ B, ∃ S' : Finset (Finset V), G.IsQuadPacking S' ∧ S'.card = S.card ∧
      (Finset.univ \ S'.biUnion id =
        (Finset.univ \ S.biUnion id).erase u ∪ {w}) ∧
      (blockSum G S' < blockSum G S ∨
        (blockSum G S' = blockSum G S ∧
          ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card ≤
            ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card)) := by
  have hu' : u ∉ S.biUnion id := (Finset.mem_sdiff.1 hu).2
  have huB : u ∉ B := fun h => hu' (Finset.subset_biUnion_of_mem id hB h)
  -- A freeable `w ∈ B`: `insert u (B.erase w)` is again a quad block.
  obtain ⟨w, hwB, hBw⟩ := IsQuadBlock.exchange (hS.1 B hB) huB h3
  -- The exchanged packing `S' = insert (insert u (B.erase w)) (S.erase B)`.
  obtain ⟨hS', hcard, hUb⟩ := hS.exchange_block hu' hB hwB hBw
  have hwU : w ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB hwB
  have hcov : Finset.univ \ (insert (insert u (B.erase w))
      (S.erase B)).biUnion id
      = (Finset.univ \ S.biUnion id).erase u ∪ {w} := by
    rw [hUb]
    exact univ_sdiff_erase_union_singleton hwU hu'
  -- Lex-maximality bounds the exchanged block's edge-sum, with the rotation
  -- bound in the equality case.
  obtain ⟨hle, hrot⟩ := lexmax_exchange hS hlex hu hB hwB hBw
  -- `blockSum` bookkeeping: only the exchanged block contributes the change.
  have hB'nin : insert u (B.erase w) ∉ S.erase B := by
    intro h
    exact hu' (Finset.subset_biUnion_of_mem id (Finset.mem_erase.1 h).2
      (Finset.mem_insert_self u _))
  have hsum1 : blockSum G (insert (insert u (B.erase w)) (S.erase B))
      = edgeSum G (insert u (B.erase w)) + blockSum G (S.erase B) := by
    simp only [blockSum]
    exact Finset.sum_insert hB'nin
  have hsum2 : blockSum G S = edgeSum G B + blockSum G (S.erase B) := by
    simp only [blockSum]
    conv_lhs => rw [← Finset.insert_erase hB]
    rw [Finset.sum_insert (Finset.notMem_erase B S)]
  refine ⟨w, hwB, _, hS', hcard, hcov, ?_⟩
  rcases hle.lt_or_eq with hlt | heq
  · exact Or.inl (by rw [hsum1, hsum2]; omega)
  · exact Or.inr ⟨by rw [hsum1, hsum2, heq], hrot heq⟩

/-- Packaged exit: after exchanging the uncovered `u` for `w ∈ B`, a
quadrilateral block `Q` inside the new leftover `(univ \ ∪S).erase u ∪ {w}`
enlarges the packing.  Wrapper around
`exists_larger_of_exchange_leftover_block` with `u ∈ univ \ ∪S` in place of
`u ∉ ∪S`. -/
theorem exists_larger_of_exchange_leftover_quad [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    {u w : V} {B : Finset V} (hu : u ∈ Finset.univ \ S.biUnion id)
    (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert u (B.erase w)))
    {Q : Finset V} (hQ : G.IsQuadBlock Q)
    (hsub : Q ⊆ (Finset.univ \ S.biUnion id).erase u ∪ {w}) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card :=
  exists_larger_of_exchange_leftover_block hS (Finset.mem_sdiff.1 hu).2
    hB hw hBw hQ hsub

/-- Glue for the `lexmax_heavy_exchange` outcome: a quadrilateral block inside
the leftover of any same-cardinality packing `S'` enlarges `S`. -/
theorem exists_larger_of_new_leftover_block [DecidableRel G.Adj]
    {S S' : Finset (Finset V)} (hS' : G.IsQuadPacking S')
    (hcard : S'.card = S.card) {Q : Finset V} (hQ : G.IsQuadBlock Q)
    (hsub : Q ⊆ Finset.univ \ S'.biUnion id) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  obtain ⟨T, hT, hlt⟩ := exists_larger_of_leftover_block hS' hQ hsub
  exact ⟨T, hT, hcard ▸ hlt⟩

end SimpleGraph
