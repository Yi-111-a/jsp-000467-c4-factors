import JSP467.CaseB
import JSP467.DegHeavy
import JSP467.UQuad
import JSP467.Base
import JSP467.Clean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# JSP-000467 — the master dichotomy for non-covering quad packings

For a quadrilateral packing `S` with `S.card < k` in a `4k`-vertex graph of
minimum degree `≥ 2k`, the leftover set `U = V ∖ ⋃S` has `4ℓ` vertices with
`ℓ = k - S.card ≥ 1`.  Either `U` already contains a quadrilateral block, or
some leftover vertex is *heavy*: it has at least three neighbours inside a
single block of `S`.

The proof splits on `ℓ`: for `ℓ = 1` a four-vertex induced subgraph of minimum
degree two already carries a quad factor (`hasQuadFactor_of_card_eq_four`);
for `ℓ = 2` and `ℓ ≥ 3` the pigeonhole lemmas of `UQuad.lean` apply once the
induced minimum degree is large enough (`≥ 4`, resp. `≥ 2ℓ - 1`).  When the
induced minimum degree is smaller, some leftover vertex has few neighbours in
`U`, hence more than `2 · S.card` neighbours among the covered vertices, and
`exists_heavy_block` pigeonholes a block containing at least three of them.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Low leftover-degree forces a heavy block (arbitrary threshold).**  If a
vertex `v` has at most `t` neighbours among the uncovered vertices, and
`2 * S.card < 2 * k - t`, then `v` has more than `2 * S.card` covered
neighbours, which pigeonhole into some block `B ∈ S` with at least three of
them. -/
theorem heavy_of_leftover_deg_le (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    {v : V} (t : ℕ)
    (hv : v ∈ Finset.univ \ S.biUnion id)
    (hdeg : ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset v).card ≤ t)
    (ht : 2 * S.card < 2 * k - t) :
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
  -- `|⋃S ∩ N v| ≥ 2k - t > 2 * S.card`.
  exact exists_heavy_block hS (by omega)

/-- **Low induced minimum degree yields a low-degree leftover vertex.**  If
the subgraph induced on `U` has minimum degree `< t`, some `v ∈ U` has fewer
than `t` neighbours inside `U`.  This is the contrapositive of
`le_minDegree_of_forall_le_degree`. -/
theorem exists_leftover_vertex_deg_lt (G : SimpleGraph V)
    [DecidableRel G.Adj] {U : Finset V} (hUne : U.Nonempty) {t : ℕ}
    (h : ¬ t ≤ (G.induce (↑U : Set V)).minDegree) :
    ∃ v ∈ U, (U ∩ G.neighborFinset v).card < t := by
  classical
  by_contra hcon
  push_neg at hcon
  apply h
  obtain ⟨u0, hu0⟩ := hUne
  haveI : Nonempty ↥(↑U : Set V) := ⟨⟨u0, Finset.mem_coe.2 hu0⟩⟩
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
  rw [hdeg, Finset.inter_comm]
  exact hcon _ hvU

/-- **Master dichotomy.**  For a non-covering quad packing with `S.card < k`,
the leftover `U = univ ∖ ⋃S` either contains a quadrilateral block or contains
a vertex with `≥ 3` neighbours in some block (`u` "heavy" on `B`). -/
theorem exists_quadBlock_or_heavy_leftover (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) (hlt : S.card < k) :
    (∃ Q : Finset V, G.IsQuadBlock Q ∧ Q ⊆ Finset.univ \ S.biUnion id) ∨
    (∃ u : V, u ∈ Finset.univ \ S.biUnion id ∧
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
    · -- Some `v ∈ U` has `deg_U(v) ≤ 1`, hence `cov(v) ≥ 2k - 1 > 2 * S.card`.
      refine Or.inr ?_
      obtain ⟨v, hvU, hvdeg⟩ := exists_leftover_vertex_deg_lt G hUne hminU
      exact ⟨v, hvU, heavy_of_leftover_deg_le G k hcard hmin hS 1 hvU
        (by omega) (by omega)⟩
  · rcases Nat.lt_or_ge ℓ 3 with hlt3 | hge3
    · -- `ℓ = 2`: `U` has eight vertices.
      have h2 : ℓ = 2 := by omega
      by_cases hminU : 4 ≤
          (G.induce (↑(Finset.univ \ S.biUnion id) : Set V)).minDegree
      · refine Or.inl ?_
        have hUcard8 : (Finset.univ \ S.biUnion id).card = 8 := by
          rw [hUcard, h2]
        exact exists_quadBlock_of_induce_minDegree_l2 G hUcard8 hUne hminU
      · -- Some `v ∈ U` has `deg_U(v) ≤ 3`, hence `cov(v) ≥ 2k - 3 > 2 * S.card`.
        refine Or.inr ?_
        obtain ⟨v, hvU, hvdeg⟩ := exists_leftover_vertex_deg_lt G hUne hminU
        exact ⟨v, hvU, heavy_of_leftover_deg_le G k hcard hmin hS 3 hvU
          (by omega) (by omega)⟩
    · -- `ℓ ≥ 3`: `U` has `4ℓ` vertices.
      by_cases hminU : 2 * ℓ - 1 ≤
          (G.induce (↑(Finset.univ \ S.biUnion id) : Set V)).minDegree
      · refine Or.inl ?_
        exact exists_quadBlock_of_induce_minDegree G hge3 hUcard hUne hminU
      · -- Some `v ∈ U` has `deg_U(v) ≤ 2ℓ - 2`, hence
        -- `cov(v) ≥ 2k - 2ℓ + 2 = 2 * S.card + 2 > 2 * S.card`.
        refine Or.inr ?_
        obtain ⟨v, hvU, hvdeg⟩ := exists_leftover_vertex_deg_lt G hUne hminU
        exact ⟨v, hvU, heavy_of_leftover_deg_le G k hcard hmin hS (2 * ℓ - 2)
          hvU (by omega) (by omega)⟩

end SimpleGraph
