import JSP467.Chord
import JSP467.RotApp
import JSP467.Exchange

/-!
# JSP-000467 — the lexicographic (chord, leftover-edge) maximizer

Wang's argument chooses the packing `S` (of a fixed cardinality) to be maximal
*first* in the total internal edge-sum of its blocks (`blockSum`, twice the
chord count τ) and *second* in the edge-sum of the leftover vertices.  We
encode the lexicographic objective as a single natural number
`blockSum * C + edgeSum` with `C = univ.card² + 1` strictly larger than any
possible `edgeSum`, so `Finset.exists_max_image` applies verbatim.

* `edgeSum_le_card_sq` — the crude bound `edgeSum G U ≤ univ.card²`.
* `exists_lexmax_packing` — existence of the lexicographic maximizer.
* `lexmax_exchange` — the packaged exchange step: swapping an uncovered `u`
  for a block vertex `w` weakly decreases the block's edge-sum, and in the
  equality case the rotation bound on leftover neighbourhoods holds.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- `edgeSum` is bounded: `edgeSum G U ≤ |U|² ≤ (card V)²`.  Indeed `edgeSum`
counts ordered adjacent pairs inside `U`, a subset of `U ×ˢ U`. -/
theorem edgeSum_le_card_sq [DecidableRel G.Adj] (U : Finset V) :
    edgeSum G U ≤ (Finset.univ : Finset V).card * (Finset.univ : Finset V).card := by
  rw [edgeSum_eq_card_filter, Finset.card_univ]
  calc ((U ×ˢ U).filter fun p => G.Adj p.1 p.2).card
      ≤ (U ×ˢ U).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = U.card * U.card := Finset.card_product _ _
    _ ≤ Fintype.card V * Fintype.card V :=
        Nat.mul_le_mul (Finset.card_le_univ _) (Finset.card_le_univ _)

/-- Lexicographic maximizer: a card-`m` packing maximizing `blockSum` first,
then the leftover `edgeSum`.  Encoded as the single `ℕ` objective
`blockSum * C + edgeSum` with `C = univ.card² + 1 > edgeSum`. -/
theorem exists_lexmax_packing [DecidableRel G.Adj] (m : ℕ)
    (hne : ∃ S : Finset (Finset V), G.IsQuadPacking S ∧ S.card = m) :
    ∃ S : Finset (Finset V), G.IsQuadPacking S ∧ S.card = m ∧
      ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = m →
        blockSum G T < blockSum G S ∨
          (blockSum G T = blockSum G S ∧
            edgeSum G (Finset.univ \ T.biUnion id) ≤
              edgeSum G (Finset.univ \ S.biUnion id)) := by
  classical
  set C : ℕ := (Finset.univ : Finset V).card * (Finset.univ : Finset V).card + 1 with hC
  set P : Finset (Finset (Finset V)) :=
    univ.filter fun S => G.IsQuadPacking S ∧ S.card = m with hPdef
  have hmem : ∀ S : Finset (Finset V),
      S ∈ P ↔ G.IsQuadPacking S ∧ S.card = m := by
    intro S
    simp [hPdef]
  obtain ⟨S₀, hS₀⟩ := hne
  have hne' : P.Nonempty := ⟨S₀, (hmem S₀).2 hS₀⟩
  obtain ⟨S, hSP, hSmax⟩ := Finset.exists_max_image P
    (fun S => blockSum G S * C + edgeSum G (Finset.univ \ S.biUnion id)) hne'
  refine ⟨S, ((hmem S).1 hSP).1, ((hmem S).1 hSP).2, ?_⟩
  intro T hT hTm
  have hle := hSmax T ((hmem T).2 ⟨hT, hTm⟩)
  have hbS : edgeSum G (Finset.univ \ S.biUnion id) < C := by
    have h := edgeSum_le_card_sq (G := G) (Finset.univ \ S.biUnion id)
    omega
  by_cases hlt : blockSum G T < blockSum G S
  · exact Or.inl hlt
  · push_neg at hlt
    -- `blockSum S ≤ blockSum T`.  Strict inequality would contradict
    -- maximality of the combined objective, since `edgeSum < C`.
    have hnotgt : ¬ blockSum G S < blockSum G T := by
      intro hcontra
      have hmul : blockSum G S * C + C ≤ blockSum G T * C := by
        have h : blockSum G S + 1 ≤ blockSum G T := hcontra
        have h' := Nat.mul_le_mul h (le_refl C)
        rwa [add_mul, one_mul] at h'
      omega
    refine Or.inr ⟨le_antisymm (not_lt.1 hnotgt) hlt, ?_⟩
    have heq : blockSum G T = blockSum G S := le_antisymm (not_lt.1 hnotgt) hlt
    rw [heq] at hle
    omega

/-- Packaged lex-max exchange step: exchanging `u ∈ U` for `w ∈ B` in the
lex-max packing weakly decreases the block's internal edge count, and if it
keeps it equal, the rotation bound holds. -/
theorem lexmax_exchange [DecidableRel G.Adj] {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    {u w : V} (hu : u ∈ Finset.univ \ S.biUnion id) {B : Finset V} (hB : B ∈ S)
    (hw : w ∈ B) (hBw : G.IsQuadBlock (insert u (B.erase w))) :
    edgeSum G (insert u (B.erase w)) ≤ edgeSum G B ∧
      (edgeSum G (insert u (B.erase w)) = edgeSum G B →
        ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card ≤
          ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card) := by
  have hu' : u ∉ S.biUnion id := (Finset.mem_sdiff.1 hu).2
  have hwU : w ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB hw
  obtain ⟨hS', hcard, hUb⟩ := hS.exchange_block hu' hB hw hBw
  -- The new block is genuinely new: it contains `u`, which no old block does.
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
  have hlexS' := hlex _ hS' hcard
  -- First component: `edgeSum` of the exchanged block does not increase.
  have hle1 : edgeSum G (insert u (B.erase w)) ≤ edgeSum G B := by
    rcases hlexS' with hlt | ⟨heq, -⟩
    · rw [hsum1, hsum2] at hlt; omega
    · rw [hsum1, hsum2] at heq; omega
  refine ⟨hle1, fun heqB => ?_⟩
  -- Equality case: `blockSum` is unchanged, so the lexicographic maximality
  -- yields the leftover `edgeSum` bound, which `edgeSum_exchange` unwraps.
  have hbeq : blockSum G (insert (insert u (B.erase w)) (S.erase B))
      = blockSum G S := by
    rw [hsum1, hsum2, heqB]
  have hcov : Finset.univ \ (insert (insert u (B.erase w))
      (S.erase B)).biUnion id
      = (Finset.univ \ S.biUnion id).erase u ∪ {w} := by
    rw [hUb]
    exact univ_sdiff_erase_union_singleton hwU hu'
  have hle2 : edgeSum G (Finset.univ \ (insert (insert u (B.erase w))
      (S.erase B)).biUnion id)
      ≤ edgeSum G (Finset.univ \ S.biUnion id) := by
    rcases hlexS' with hlt | ⟨-, hle⟩
    · rw [hbeq] at hlt; omega
    · exact hle
  rw [hcov] at hle2
  have hwU' : w ∉ Finset.univ \ S.biUnion id :=
    fun h => (Finset.mem_sdiff.1 h).2 hwU
  rw [edgeSum_exchange _ hu hwU'] at hle2
  omega

end SimpleGraph
