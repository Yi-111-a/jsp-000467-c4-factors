import JSP467.LexMax
import JSP467.CaseB
import JSP467.Clean
import JSP467.Chord
import JSP467.Rotate

/-!
# JSP-000467 — frontier reduction: enlargement via the lex-max heavy case

Wang's enlargement argument (Wa10) works with a packing that is
*lexicographically* maximal among packings of the same cardinality: first in
`blockSum` (twice the chord count of the blocks), then in the `edgeSum` of the
leftover vertices.  This file sharpens the frontier of the formalization:

* `wang_heavy_lex` — the residual core: a lexicographically maximal
  non-covering packing carrying a heavy vertex can be enlarged.  This is the
  single remaining `sorry` of the file (the Wa10 switching argument).
* `exists_larger_quadPacking_of_lexmax` — every non-covering packing `S` is
  dominated by a lex-max packing `S'` of the same cardinality; `S'` is still
  non-covering, hence either clean (handled by
  `exists_larger_quadPacking_of_clean`) or heavy (handled by `wang_heavy_lex`).
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Remaining core of Wang (Wa10).** A lexicographically maximal
(card, then `blockSum`, then leftover `edgeSum`) non-covering quadrilateral
packing that carries a heavy vertex can be enlarged.  This is the residual
switching argument of Wa10. -/
theorem wang_heavy_lex (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hk : 1 ≤ k) (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) (hlt : S.card < k)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    (hheavy : ∃ u : V, u ∉ S.biUnion id ∧
      ∃ B ∈ S, 3 ≤ (B ∩ G.neighborFinset u).card) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  sorry

/-- **Enlargement reduced to the heavy lex-max case.** Every non-covering
packing `S` is dominated by a lex-max packing `S'` of the same cardinality;
`S'` is still non-covering, so it is either clean (handled by
`exists_larger_quadPacking_of_clean`) or carries a heavy vertex
(`wang_heavy_lex`). -/
theorem exists_larger_quadPacking_of_lexmax (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hncov : S.biUnion id ≠ Finset.univ) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  classical
  -- The blocks of `S` are pairwise disjoint sets of four vertices.
  have hdisj : (S : Set (Finset V)).PairwiseDisjoint id :=
    fun B hB C hC hne => hS.2 B hB C hC hne
  have hScard : (S.biUnion id).card = 4 * S.card := by
    calc (S.biUnion id).card
        = ∑ B ∈ S, (id B).card := Finset.card_biUnion hdisj
      _ = ∑ _B ∈ S, 4 := Finset.sum_congr rfl fun B hB => (hS.1 B hB).1
      _ = 4 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- Non-covering means strictly fewer than `k` blocks.
  have hlt : S.card < k := by
    have hss : S.biUnion id ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ _, hncov⟩
    have hclt : (S.biUnion id).card < Fintype.card V := by
      have h := Finset.card_lt_card hss
      rwa [Finset.card_univ] at h
    rw [hScard, hcard] at hclt
    omega
  -- Pass to a lexicographically maximal packing of the same cardinality.
  obtain ⟨S', hS', hm, hlex⟩ :=
    exists_lexmax_packing (G := G) S.card ⟨S, hS, rfl⟩
  -- `S'` has the same cardinality, so it also fails to cover every vertex.
  have hS'ncov : S'.biUnion id ≠ Finset.univ := by
    intro hcon
    have hdisj' : (S' : Set (Finset V)).PairwiseDisjoint id :=
      fun B hB C hC hne => hS'.2 B hB C hC hne
    have hS'card : (S'.biUnion id).card = 4 * S'.card := by
      calc (S'.biUnion id).card
          = ∑ B ∈ S', (id B).card := Finset.card_biUnion hdisj'
        _ = ∑ _B ∈ S', 4 := Finset.sum_congr rfl fun B hB => (hS'.1 B hB).1
        _ = 4 * S'.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have heq : (S'.biUnion id).card = Fintype.card V := by
      rw [hcon, Finset.card_univ]
    rw [hS'card, hcard, hm] at heq
    omega
  -- Case split: `S'` is either clean or carries a heavy vertex.
  rcases clean_or_exists_heavy G (S := S') with hclean | hheavy
  · obtain ⟨T, hT, hTlt⟩ :=
      exists_larger_quadPacking_of_clean G k hk hcard hmin hS' hS'ncov hclean
    exact ⟨T, hT, hm ▸ hTlt⟩
  · obtain ⟨T, hT, hTlt⟩ :=
      wang_heavy_lex G k hk hcard hmin hS' (hm.symm ▸ hlt)
        (fun T hT hTm => hlex T hT (hTm.trans hm)) hheavy
    exact ⟨T, hT, hm ▸ hTlt⟩

end SimpleGraph
