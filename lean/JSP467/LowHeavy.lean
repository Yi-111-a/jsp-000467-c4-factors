import JSP467.QuadOrHeavy
import JSP467.Exchange

/-!
# JSP-000467 — refined dichotomy exposing the leftover-degree bound

`exists_quadBlock_or_heavy_leftover` (QuadOrHeavy.lean) establishes that a
non-covering quadrilateral packing `S` (`S.card < k`) either leaves a
quadrilateral block inside the leftover `U = univ ∖ ⋃S`, or has a leftover
vertex that is *heavy* on some block (`≥ 3` neighbours inside it).  Its proof
in fact produces a vertex whose *leftover degree* is bounded; exposing that
bound is the point of the present file.

Writing `ℓ = k - S.card` (so `|U| = 4ℓ`), the three branches of the master
dichotomy yield:

* `ℓ = 1`: some `u ∈ U` with `deg_U u < 2`, i.e. `deg_U u ≤ 1 = 2ℓ - 1`;
* `ℓ = 2`: some `u ∈ U` with `deg_U u < 4`, i.e. `deg_U u ≤ 3 = 2ℓ - 1`;
* `ℓ ≥ 3`: some `u ∈ U` with `deg_U u < 2ℓ - 1`, i.e. `deg_U u ≤ 2ℓ - 2`.

The uniform bound `deg_U u ≤ 2ℓ - 1` therefore holds in every case, and it is
still strong enough to force heaviness: `u` has at least
`2k - (2ℓ - 1) = 2·S.card + 1 > 2·S.card` covered neighbours, which pigeonhole
(`exists_heavy_block`) into some `B ∈ S` containing three of them.

* `exists_quadBlock_or_heavy_lowdeg` — the refined dichotomy.
* `exists_heavy_lowdeg_of_no_larger` — corollary for `by_contra` arguments:
  when no strictly larger packing exists, the first alternative is killed by
  `exists_larger_of_leftover_block`, leaving a low-leftover-degree heavy
  vertex.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Refined dichotomy.**  For a non-covering quad packing with
`S.card < k`, the leftover `U = univ ∖ ⋃S` either contains a quadrilateral
block or contains a vertex `u` whose leftover degree is at most
`2 * (k - S.card) - 1` and which has `≥ 3` neighbours in some block of `S`. -/
theorem exists_quadBlock_or_heavy_lowdeg (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) (hlt : S.card < k) :
    (∃ Q : Finset V, G.IsQuadBlock Q ∧ Q ⊆ Finset.univ \ S.biUnion id) ∨
    (∃ u : V, u ∈ Finset.univ \ S.biUnion id ∧
      ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card
        ≤ 2 * (k - S.card) - 1 ∧
      ∃ B ∈ S, 3 ≤ (B ∩ G.neighborFinset u).card) := by
  classical
  have hS' := hS
  obtain ⟨hblk, hpair⟩ := hS'
  -- The blocks of `S` are pairwise disjoint sets of four vertices.
  have hdisj : (S : Set (Finset V)).PairwiseDisjoint id :=
    fun B hB C hC hne => hpair B hB C hC hne
  have hScard : (S.biUnion id).card = 4 * S.card := by
    calc (S.biUnion id).card
        = ∑ B ∈ S, (id B).card := Finset.card_biUnion hdisj
      _ = ∑ _B ∈ S, 4 := Finset.sum_congr rfl fun B hB => (hblk B hB).1
      _ = 4 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- Hence the leftover `U` has exactly `4 * (k - S.card)` vertices.
  have hUcard : (Finset.univ \ S.biUnion id).card = 4 * (k - S.card) := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (S.biUnion id))
    rw [Finset.card_univ, hcard, hScard] at h
    omega
  set ℓ := k - S.card with hℓ
  have hℓpos : 1 ≤ ℓ := by omega
  have hUne : (Finset.univ \ S.biUnion id).Nonempty := by
    rw [← Finset.card_pos, hUcard]
    omega
  have hGUcard :
      Fintype.card ↥(↑(Finset.univ \ S.biUnion id) : Set V) = 4 * ℓ := by
    have hc : Fintype.card ↥(↑(Finset.univ \ S.biUnion id) : Set V)
        = (Finset.univ \ S.biUnion id).card := by
      rw [← Set.toFinset_card, Finset.toFinset_coe]
    rw [hc, hUcard]
  have hUne' := hUne
  obtain ⟨u0, hu0⟩ := hUne'
  haveI : Nonempty ↥(↑(Finset.univ \ S.biUnion id) : Set V) :=
    ⟨⟨u0, Finset.mem_coe.2 hu0⟩⟩
  rcases Nat.lt_or_ge ℓ 2 with hlt2 | hge2
  · -- `ℓ = 1`: `U` has four vertices.
    have h1 : ℓ = 1 := by omega
    by_cases hminU : 2 ≤
        (G.induce (↑(Finset.univ \ S.biUnion id) : Set V)).minDegree
    · -- The induced subgraph on `U` is itself a quad factor.
      refine Or.inl ?_
      have hcard4' :
          Fintype.card ↥(↑(Finset.univ \ S.biUnion id) : Set V) = 4 := by
        rw [hGUcard, h1]
      obtain ⟨S', hS'blk, -, hS'cov⟩ :=
        hasQuadFactor_of_card_eq_four
          (G.induce (↑(Finset.univ \ S.biUnion id) : Set V)) hcard4' hminU
      have hS'ne : S'.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne, Finset.biUnion_empty] at hS'cov
        exact Finset.univ_nonempty.ne_empty hS'cov.symm
      obtain ⟨t, ht⟩ := hS'ne
      obtain ⟨hQblk, hQsub⟩ := IsQuadBlock.of_induce (hS'blk t ht)
      exact ⟨t.image Subtype.val, hQblk,
        fun x hx => Finset.mem_coe.1 (hQsub x hx)⟩
    · -- Some `v ∈ U` has `deg_U(v) ≤ 1 = 2ℓ - 1`, hence
      -- `cov(v) ≥ 2k - 1 > 2 * S.card`.
      refine Or.inr ?_
      obtain ⟨v, hvU, hvdeg⟩ := exists_leftover_vertex_deg_lt G hUne hminU
      exact ⟨v, hvU, by omega, heavy_of_leftover_deg_le G k hcard hmin hS 1
        hvU (by omega) (by omega)⟩
  · rcases Nat.lt_or_ge ℓ 3 with hlt3 | hge3
    · -- `ℓ = 2`: `U` has eight vertices.
      have h2 : ℓ = 2 := by omega
      by_cases hminU : 4 ≤
          (G.induce (↑(Finset.univ \ S.biUnion id) : Set V)).minDegree
      · refine Or.inl ?_
        have hUcard8 : (Finset.univ \ S.biUnion id).card = 8 := by
          rw [hUcard, h2]
        exact exists_quadBlock_of_induce_minDegree_l2 G hUcard8 hUne hminU
      · -- Some `v ∈ U` has `deg_U(v) ≤ 3 = 2ℓ - 1`, hence
        -- `cov(v) ≥ 2k - 3 > 2 * S.card`.
        refine Or.inr ?_
        obtain ⟨v, hvU, hvdeg⟩ := exists_leftover_vertex_deg_lt G hUne hminU
        exact ⟨v, hvU, by omega, heavy_of_leftover_deg_le G k hcard hmin hS 3
          hvU (by omega) (by omega)⟩
    · -- `ℓ ≥ 3`: `U` has `4ℓ` vertices.
      by_cases hminU : 2 * ℓ - 1 ≤
          (G.induce (↑(Finset.univ \ S.biUnion id) : Set V)).minDegree
      · refine Or.inl ?_
        exact exists_quadBlock_of_induce_minDegree G hge3 hUcard hUne hminU
      · -- Some `v ∈ U` has `deg_U(v) ≤ 2ℓ - 2 < 2ℓ - 1`, hence
        -- `cov(v) ≥ 2k - 2ℓ + 2 = 2 * S.card + 2 > 2 * S.card`.
        refine Or.inr ?_
        obtain ⟨v, hvU, hvdeg⟩ := exists_leftover_vertex_deg_lt G hUne hminU
        exact ⟨v, hvU, by omega,
          heavy_of_leftover_deg_le G k hcard hmin hS (2 * ℓ - 2)
            hvU (by omega) (by omega)⟩

/-- **Corollary for `by_contra`.**  If no strictly larger quadrilateral
packing exists, then a non-covering packing `S` has a leftover vertex `u`
whose leftover degree is at most `2 * (k - S.card) - 1` and which is heavy on
some block of `S`. -/
theorem exists_heavy_lowdeg_of_no_larger (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) (hlt : S.card < k)
    (hnolarger : ¬ ∃ T : Finset (Finset V),
      G.IsQuadPacking T ∧ S.card < T.card) :
    ∃ u : V, u ∈ Finset.univ \ S.biUnion id ∧
      ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card
        ≤ 2 * (k - S.card) - 1 ∧
      ∃ B ∈ S, 3 ≤ (B ∩ G.neighborFinset u).card := by
  rcases exists_quadBlock_or_heavy_lowdeg G k hcard hmin hS hlt with hQ | h
  · -- A quad block inside the leftover would enlarge the packing.
    obtain ⟨Q, hQblk, hQsub⟩ := hQ
    exact absurd (exists_larger_of_leftover_block hS hQblk hQsub) hnolarger
  · exact h

end SimpleGraph
