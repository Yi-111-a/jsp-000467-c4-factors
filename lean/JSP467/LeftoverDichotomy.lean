import JSP467.CaseB
import JSP467.DegHeavy
import JSP467.UQuad
import JSP467.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# JSP-000467 — the leftover dichotomy (iteration engine)

For a non-covering quadrilateral packing `S` with leftover
`U := univ \ S.biUnion id` (a set of `4 * (k - S.card)` vertices), exactly one
of the following holds:

* `U` contains a quadrilateral block `Q` of `G` — the packing can be enlarged
  directly (`exists_larger_quadPacking_of_leftover`); or
* some uncovered vertex `v` has at least three neighbours inside a single
  block `B ∈ S` — the "heavy" configuration handled by the switching
  arguments.

The proof splits on the minimum leftover-degree.  If some `v ∈ U` has at most
`2 * (k - S.card) - 1` neighbours inside `U`, then it has strictly more than
`2 * S.card` neighbours inside the covered set, and pigeonhole
(`exists_heavy_block`) yields a heavy block — this is
`exists_heavy_block_of_low_leftover_degree'`, a relaxation by one of
`exists_heavy_block_of_low_leftover_degree` from `DegHeavy.lean`.
Otherwise every leftover vertex has at least `2 * (k - S.card)` neighbours
inside `U`, so the induced subgraph has minimum degree `≥ 2 * (k - S.card)`
and the usual `ℓ = 1` / `ℓ ≥ 2` dichotomy (`hasQuadFactor_of_card_eq_four`
resp. `exists_isQuadBlock_self`) produces a block inside `U`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Relaxed low-leftover-degree pigeonhole.**  If `v` is uncovered and has
at most `2 * (k - S.card) - 1` neighbours among the uncovered vertices, then
its `≥ 2k - (2 * (k - S.card) - 1) = 2 * S.card + 1` covered neighbours
pigeonhole into some block with at least three of them.  This weakens the
bound of `exists_heavy_block_of_low_leftover_degree` (`≤ 2 * (k - S.card) - 2`)
by one; the arithmetic still closes since `2 * S.card + 1 > 2 * S.card`. -/
theorem exists_heavy_block_of_low_leftover_degree' (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hlt : S.card < k) {v : V}
    (hv : v ∈ Finset.univ \ S.biUnion id)
    (hdeg : ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset v).card
      ≤ 2 * (k - S.card) - 1) :
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
  -- `|⋃S ∩ N v| ≥ 2k - (2 * (k - S.card) - 1) = 2 * S.card + 1 > 2 * S.card`.
  exact exists_heavy_block hS (by omega)

/-- **The leftover dichotomy.**  For any non-covering quadrilateral packing
`S`, either the leftover `univ \ ⋃S` already contains a quadrilateral block of
`G`, or some leftover vertex is *heavy*: it has at least three neighbours
inside a single block of `S`. -/
theorem exists_quadBlock_or_exists_heavy
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hncov : S.biUnion id ≠ Finset.univ) :
    (∃ Q : Finset V, G.IsQuadBlock Q ∧ Q ⊆ Finset.univ \ S.biUnion id) ∨
    (∃ v : V, v ∈ Finset.univ \ S.biUnion id ∧
      ∃ B ∈ S, 3 ≤ (B ∩ G.neighborFinset v).card) := by
  classical
  obtain ⟨hblk, hpair⟩ := hS
  set U : Finset V := Finset.univ \ S.biUnion id with hU_def
  -- The set `U` of uncovered vertices is nonempty.
  obtain ⟨u0, hu0⟩ : ∃ u, u ∈ U := by
    have hss : S.biUnion id ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ _, hncov⟩
    obtain ⟨x, -, hx⟩ := Finset.exists_of_ssubset hss
    exact ⟨x, Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hx⟩⟩
  have hUne : U.Nonempty := ⟨u0, hu0⟩
  haveI : Nonempty ↥(↑U : Set V) := ⟨⟨u0, Finset.mem_coe.2 hu0⟩⟩
  have hUpos : 0 < U.card := Finset.card_pos.2 hUne
  -- The blocks of `S` are pairwise disjoint sets of four vertices.
  have hdisj : (S : Set (Finset V)).PairwiseDisjoint id :=
    fun B hB C hC hne => hpair B hB C hC hne
  have hScard : (S.biUnion id).card = 4 * S.card := by
    calc (S.biUnion id).card
        = ∑ B ∈ S, (id B).card := Finset.card_biUnion hdisj
      _ = ∑ _B ∈ S, 4 := Finset.sum_congr rfl fun B hB => (hblk B hB).1
      _ = 4 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- Hence `U` has exactly `4 * (k - S.card)` vertices, and `S.card < k`.
  have hUcard : U.card = 4 * (k - S.card) := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (S.biUnion id))
    rw [Finset.card_univ, hcard, hScard, ← hU_def] at h
    omega
  have hGUcard : Fintype.card ↥(↑U : Set V) = 4 * (k - S.card) := by
    have hc : Fintype.card ↥(↑U : Set V) = U.card := by
      rw [← Set.toFinset_card, Finset.toFinset_coe]
    rw [hc, hUcard]
  have hlt : S.card < k := by omega
  -- Case split on the minimum leftover-degree.
  by_cases hlow : ∃ v ∈ U, (U ∩ G.neighborFinset v).card ≤ 2 * (k - S.card) - 1
  · -- **Case A:** some `v ∈ U` has low leftover-degree; it is heavy.
    obtain ⟨v, hvU, hvdeg⟩ := hlow
    refine Or.inr ⟨v, hvU, ?_⟩
    exact exists_heavy_block_of_low_leftover_degree' G k hcard hmin
      ⟨hblk, hpair⟩ hlt (hU_def ▸ hvU) (hU_def ▸ hvdeg)
  · -- **Case B:** every `v ∈ U` has at least `2 * (k - S.card)` leftover
    -- neighbours, so `G.induce ↑U` has minimum degree `≥ 2 * (k - S.card)`.
    push_neg at hlow
    have hUdeg : ∀ u ∈ U, 2 * (k - S.card) ≤ (G.neighborFinset u ∩ U).card := by
      intro u hu
      have h := hlow u hu
      rw [Finset.inter_comm]
      omega
    have hGUmin : 2 * (k - S.card) ≤ (G.induce (↑U : Set V)).minDegree := by
      refine (G.induce (↑U : Set V)).le_minDegree_of_forall_le_degree _ fun v => ?_
      have hvU : (v : V) ∈ U := Finset.mem_coe.1 v.2
      have hmap := congrArg Finset.card (G.map_neighborFinset_induce v)
      rw [Finset.card_map, Finset.toFinset_coe] at hmap
      have hdeg : (G.induce (↑U : Set V)).degree v
          = (G.neighborFinset (v : V) ∩ U).card := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hmap]
        congr 1
        ext w
        simp only [SimpleGraph.mem_neighborFinset]
      rw [hdeg]
      exact hUdeg _ hvU
    -- Find a quadrilateral block of `G` inside `U`.
    obtain ⟨Q, hQblk, hQU⟩ : ∃ Q : Finset V, G.IsQuadBlock Q ∧ Q ⊆ U := by
      by_cases hℓ : k - S.card = 1
      · -- `U` has four vertices and the induced graph has minimum degree two.
        have hcard4' : Fintype.card ↥(↑U : Set V) = 4 := by
          rw [hGUcard, hℓ]
        have hmin2 : 2 ≤ (G.induce (↑U : Set V)).minDegree := by
          have h := hGUmin
          omega
        obtain ⟨S', hS'blk, -, hS'cov⟩ :=
          hasQuadFactor_of_card_eq_four (G.induce (↑U : Set V)) hcard4' hmin2
        have hS'ne : S'.Nonempty := by
          by_contra hne
          rw [Finset.not_nonempty_iff_eq_empty] at hne
          rw [hne, Finset.biUnion_empty] at hS'cov
          exact Finset.univ_nonempty.ne_empty hS'cov.symm
        obtain ⟨t, ht⟩ := hS'ne
        obtain ⟨hQblk, hQsub⟩ := IsQuadBlock.of_induce (hS'blk t ht)
        exact ⟨t.image Subtype.val, hQblk,
          fun x hx => Finset.mem_coe.1 (hQsub x hx)⟩
      · -- `U` has `4 * ℓ` vertices with `ℓ ≥ 2`: use the pigeonhole lemma.
        have hℓ2 : 2 ≤ k - S.card := by omega
        obtain ⟨v0⟩ : Nonempty ↥(↑U : Set V) := ⟨⟨u0, Finset.mem_coe.2 hu0⟩⟩
        have hbig : Fintype.card ↥(↑U : Set V)
            < 2 * (k - S.card) * (2 * (k - S.card) - 1) + 1 := by
          rw [hGUcard]
          have h3 : 3 ≤ 2 * (k - S.card) - 1 := by omega
          have h4 : 2 * (k - S.card) * 3
              ≤ 2 * (k - S.card) * (2 * (k - S.card) - 1) :=
            Nat.mul_le_mul le_rfl h3
          omega
        obtain ⟨t, htb, -⟩ :=
          (G.induce (↑U : Set V)).exists_isQuadBlock_self v0 hGUmin hbig
        obtain ⟨hQblk, hQsub⟩ := IsQuadBlock.of_induce htb
        exact ⟨t.image Subtype.val, hQblk,
          fun x hx => Finset.mem_coe.1 (hQsub x hx)⟩
    exact Or.inl ⟨Q, hQblk, hQU⟩

end SimpleGraph
