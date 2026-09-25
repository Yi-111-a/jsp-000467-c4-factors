import JSP467.LexMax

/-!
# JSP-000467 — reduction of the enlargement step to lex-max packings

To prove that every non-covering quadrilateral packing can be enlarged, it
suffices to prove it for packings that are *lexicographically maximal*:
maximal first in the total internal edge-sum of the blocks (`blockSum`), and
second in the edge-sum of the uncovered vertices.

The argument is a one-line cardinality observation plus `exists_lexmax_packing`:
a non-covering packing `S` satisfies `S.card < k` (its blocks are pairwise
disjoint four-sets whose union is a proper subset of the `4k` vertices), so we
may replace `S` by a lex-max packing `S₀` of the same (still `< k`) cardinality
and apply the lex-max enlargement hypothesis to `S₀`.

* `IsQuadPacking.card_lt_of_not_covering` — a non-covering packing has
  fewer than `k` blocks.
* `exists_larger_quadPacking_of_lexmax_step` — the reduction lemma.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A non-covering quadrilateral packing on `4k` vertices has strictly fewer
than `k` blocks: the blocks are pairwise-disjoint four-sets, so their union has
`4 * S.card < 4k` elements. -/
theorem IsQuadPacking.card_lt_of_not_covering {G : SimpleGraph V}
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hncov : S.biUnion id ≠ Finset.univ) :
    S.card < k := by
  classical
  obtain ⟨hblk, hpair⟩ := hS
  have hdisj : (S : Set (Finset V)).PairwiseDisjoint id :=
    fun B hB C hC hne => hpair B hB C hC hne
  have hScard : (S.biUnion id).card = 4 * S.card := by
    calc (S.biUnion id).card
        = ∑ B ∈ S, (id B).card := Finset.card_biUnion hdisj
      _ = ∑ _B ∈ S, 4 := Finset.sum_congr rfl fun B hB => (hblk B hB).1
      _ = 4 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hss : S.biUnion id ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ _, hncov⟩
  have hlt := Finset.card_lt_card hss
  rw [Finset.card_univ, hcard, hScard] at hlt
  omega

set_option linter.unusedVariables false in
/-- **Reduction to the lex-max case.**  To enlarge an arbitrary non-covering
quadrilateral packing `S`, it suffices to enlarge packings of cardinality
`< k` that are lexicographically maximal (in `blockSum`, then in the leftover
`edgeSum`): replace `S` by a lex-max packing `S₀` of the same cardinality and
apply the hypothesis to `S₀`. -/
theorem exists_larger_quadPacking_of_lexmax_step
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (hk : 1 ≤ k)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    (hlex : ∀ {S : Finset (Finset V)}, G.IsQuadPacking S →
      S.card < k →
      (∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
        blockSum G T < blockSum G S ∨
          (blockSum G T = blockSum G S ∧
            edgeSum G (Finset.univ \ T.biUnion id) ≤
              edgeSum G (Finset.univ \ S.biUnion id))) →
      ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hncov : S.biUnion id ≠ Finset.univ) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  classical
  -- Non-covering forces `S.card < k`.
  have hSlt : S.card < k := hS.card_lt_of_not_covering hcard hncov
  -- Replace `S` by a lex-max packing `S₀` of the same cardinality.
  obtain ⟨S₀, hS₀, hS₀card, hS₀lex⟩ :=
    exists_lexmax_packing (m := S.card) ⟨S, hS, rfl⟩
  -- `S₀.card = S.card < k`, so the lex-max enlargement hypothesis applies.
  have hS₀lt : S₀.card < k := hS₀card ▸ hSlt
  obtain ⟨T, hT, hTcard⟩ := hlex hS₀ hS₀lt
    fun T hT hTc => hS₀lex T hT (hTc.trans hS₀card)
  exact ⟨T, hT, hS₀card ▸ hTcard⟩

end SimpleGraph
