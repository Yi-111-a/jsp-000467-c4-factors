import JSP467.LexMax
import JSP467.Exchange
import JSP467.Rotate
import JSP467.Pairing
import JSP467.Chord

/-!
# JSP-000467 — one packaged step of the switching cascade

Wang's switching argument repeatedly exchanges a leftover vertex `u` that is
heavy on some block `B` (≥ 3 neighbours inside `B`) for a freeable vertex
`w ∈ B`.  This module packages a *single* such step at a packing that is
lexicographically maximal in `(blockSum, leftover edgeSum)`:

* `exists_exchange_step_lex` — the exchange produces a same-cardinality
  packing `S'` whose leftover is `(U \ {u}) ∪ {w}`, whose `blockSum` does not
  increase, and when `blockSum` is preserved the freed `w` has no more
  leftover neighbours than `u` had (the rotation bound).
* `exists_larger_or_exchange_step` — the chained version: either the new
  leftover contains a quadrilateral block (so the packing enlarges), or the
  step data together with the rotation bound is returned.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Packaged exchange step at a lex-max packing.  A leftover vertex `u` with
≥3 neighbours in block `B` can be swapped for some `w ∈ B`; the exchanged
packing `S'` has the same cardinality, leftover `U\{u}∪{w}`, no larger
`blockSum`, and when `blockSum` is preserved the freed `w` has no more
leftover neighbours than `u` had (rotation bound). -/
theorem exists_exchange_step_lex [DecidableRel G.Adj] {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    {u : V} (hu : u ∈ Finset.univ \ S.biUnion id)
    {B : Finset V} (hB : B ∈ S)
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    ∃ (S' : Finset (Finset V)) (w : V),
      G.IsQuadPacking S' ∧ S'.card = S.card ∧
      Finset.univ \ S'.biUnion id
        = (Finset.univ \ S.biUnion id).erase u ∪ {w} ∧
      w ∈ B ∧ w ≠ u ∧
      blockSum G S' ≤ blockSum G S ∧
      (blockSum G S' = blockSum G S →
        ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card ≤
          ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card) := by
  have hu' : u ∉ S.biUnion id := (Finset.mem_sdiff.1 hu).2
  have huB : u ∉ B := fun h => hu' (Finset.subset_biUnion_of_mem id hB h)
  -- Pick the first of the two freeable vertices.
  obtain ⟨w, w₂, hwB, -, -, hBw, -⟩ :=
    exists_two_freeable (hS.1 B hB) huB h3
  have hwU : w ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB hwB
  have hne : w ≠ u := fun h => hu' (h ▸ hwU)
  -- The exchanged packing `S' = insert (insert u (B.erase w)) (S.erase B)`.
  obtain ⟨hS', hcard, hUb⟩ := hS.exchange_block hu' hB hwB hBw
  -- Lex-maximality: the exchanged block's edge-sum does not increase, and
  -- in the equality case the rotation bound holds.
  obtain ⟨hle1, hrot⟩ := lexmax_exchange hS hlex hu hB hwB hBw
  -- `blockSum` splits off the exchanged block on both sides.
  have hB'nin : insert u (B.erase w) ∉ S.erase B := by
    intro h
    exact hu' (Finset.subset_biUnion_of_mem id (Finset.mem_erase.1 h).2
      (Finset.mem_insert_self u _))
  have hsum1 : blockSum G (insert (insert u (B.erase w)) (S.erase B))
      = edgeSum G (insert u (B.erase w)) + blockSum G (S.erase B) := by
    simp only [blockSum]
    exact Finset.sum_insert hB'nin
  have hsum2 : blockSum G S
      = edgeSum G B + blockSum G (S.erase B) := by
    simp only [blockSum]
    conv_lhs => rw [← Finset.insert_erase hB]
    rw [Finset.sum_insert (Finset.notMem_erase B S)]
  have hsumle : blockSum G (insert (insert u (B.erase w)) (S.erase B))
      ≤ blockSum G S := by omega
  refine ⟨insert (insert u (B.erase w)) (S.erase B), w, hS', hcard, ?_, hwB,
    hne, hsumle, fun heq => ?_⟩
  · rw [hUb]
    exact univ_sdiff_erase_union_singleton hwU hu'
  · -- `blockSum` preserved forces `edgeSum` of the exchanged block preserved.
    have heqB : edgeSum G (insert u (B.erase w)) = edgeSum G B := by omega
    exact hrot heqB

/-- Chained version: in a lex-max packing, either the leftover of the
exchanged packing contains a quad block (enlargement), or the freed vertex
inherits the low-leftover-degree bound. -/
theorem exists_larger_or_exchange_step [DecidableRel G.Adj]
    {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    {u : V} (hu : u ∈ Finset.univ \ S.biUnion id)
    {B : Finset V} (hB : B ∈ S)
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    (∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card) ∨
    (∃ S' w, G.IsQuadPacking S' ∧ S'.card = S.card ∧
      Finset.univ \ S'.biUnion id
        = (Finset.univ \ S.biUnion id).erase u ∪ {w} ∧
      w ∈ B ∧ blockSum G S' ≤ blockSum G S ∧
      (blockSum G S' = blockSum G S →
        ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card ≤
          ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card) ∧
      ¬ ∃ Q : Finset V, G.IsQuadBlock Q ∧
        Q ⊆ Finset.univ \ S'.biUnion id) := by
  obtain ⟨S', w, hS', hcard, hUb, hwB, -, hsum, hrot⟩ :=
    exists_exchange_step_lex hS hlex hu hB h3
  by_cases hQ : ∃ Q : Finset V, G.IsQuadBlock Q ∧
      Q ⊆ Finset.univ \ S'.biUnion id
  · -- A quad block in the new leftover enlarges `S'` beyond `S.card`.
    obtain ⟨Q, hQb, hQsub⟩ := hQ
    obtain ⟨T, hT, hTcard⟩ := exists_larger_of_leftover_block hS' hQb hQsub
    exact Or.inl ⟨T, hT, by omega⟩
  · exact Or.inr ⟨S', w, hS', hcard, hUb, hwB, hsum, hrot, hQ⟩

end SimpleGraph
