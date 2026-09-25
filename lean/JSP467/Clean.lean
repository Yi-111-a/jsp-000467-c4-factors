import JSP467.Main
import JSP467.Base
import JSP467.Through
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# JSP-000467 — the "clean" case of the packing-enlargement argument

If a quadrilateral packing `S` fails to cover every vertex and every uncovered
vertex has at most two neighbours inside each block of `S`, then `S` can be
enlarged: the uncovered vertices induce a subgraph on `4 * (k - S.card)`
vertices with minimum degree at least `2 * (k - S.card)`, which therefore
already contains a quadrilateral block disjoint from every block of `S`.

The main statement is `exists_larger_quadPacking_of_clean`, together with the
lifting lemma `IsQuadBlock.of_induce` for blocks of induced subgraphs.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A quadrilateral block of an induced subgraph `G.induce s` lifts to a
quadrilateral block of `G`, namely the image of the block under the inclusion
`↥s ↪ V`. -/
theorem IsQuadBlock.of_induce {G : SimpleGraph V} {s : Set V} {t : Finset ↥s}
    (h : (G.induce s).IsQuadBlock t) :
    G.IsQuadBlock (t.image Subtype.val) ∧ ∀ x ∈ t.image Subtype.val, x ∈ s := by
  obtain ⟨hc, ⟨f⟩⟩ := h
  have hcard : (t.image Subtype.val).card = 4 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, hc]
  have hsub : ∀ x ∈ t.image Subtype.val, x ∈ s := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, -, rfl⟩ := hx
    exact a.2
  refine ⟨⟨hcard, ⟨?_⟩⟩, hsub⟩
  -- The inclusion `↥t ↪ ↥(t.image Subtype.val)` transports the copy of `C₄`.
  let e : ↥(↑t : Set ↥s) → ↥(↑(t.image Subtype.val) : Set V) :=
    fun a => ⟨a.1.1,
      Finset.mem_coe.2 (Finset.mem_image.2 ⟨a.1, Finset.mem_coe.1 a.2, rfl⟩)⟩
  have hmap : ∀ {u v : ↥(↑t : Set ↥s)},
      ((G.induce s).induce (↑t : Set ↥s)).Adj u v →
      (G.induce (↑(t.image Subtype.val) : Set V)).Adj (e u) (e v) :=
    fun huv => induce_adj.2 (induce_adj.1 (induce_adj.1 huv))
  have he : Function.Injective e := fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg Subtype.val hab))
  exact (Hom.toCopy
    (⟨e, fun huv => hmap huv⟩ :
      (G.induce s).induce (↑t : Set ↥s) →g
        G.induce (↑(t.image Subtype.val) : Set V)) he).comp f

/-- **Clean case of the enlargement step.**  If a quadrilateral packing `S`
does not cover all vertices, and every uncovered vertex has at most two
neighbours inside each block of `S`, then `S` is not maximal: the uncovered
vertices contain a quadrilateral block that can be added to `S`. -/
theorem exists_larger_quadPacking_of_clean (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k) (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hncov : S.biUnion id ≠ Finset.univ)
    (hclean : ∀ u : V, u ∉ S.biUnion id → ∀ B ∈ S, (B ∩ G.neighborFinset u).card ≤ 2) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  classical
  obtain ⟨hblk, hpair⟩ := hS
  set U : Finset V := Finset.univ \ S.biUnion id with hU_def
  -- The set `U` of uncovered vertices is nonempty.
  have hUne : U.Nonempty := by
    have hss : S.biUnion id ⊂ Finset.univ :=
      Finset.ssubset_iff_subset_ne.2 ⟨Finset.subset_univ _, hncov⟩
    obtain ⟨x, -, hx⟩ := Finset.exists_of_ssubset hss
    exact ⟨x, Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨u0, hu0⟩ := hUne
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
  -- Hence `U` has exactly `4 * (k - S.card)` vertices.
  have hUcard : U.card = 4 * (k - S.card) := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (S.biUnion id))
    rw [Finset.card_univ, hcard, hScard, ← hU_def] at h
    omega
  have hGUcard : Fintype.card ↥(↑U : Set V) = 4 * (k - S.card) := by
    have hc : Fintype.card ↥(↑U : Set V) = U.card := by
      rw [← Set.toFinset_card, Finset.toFinset_coe]
    rw [hc, hUcard]
  -- Each `u ∈ U` has at most `2 * S.card` neighbours inside the union of `S`.
  have hle : ∀ u ∈ U, (S.biUnion id ∩ G.neighborFinset u).card ≤ 2 * S.card := by
    intro u hu
    have hu' : u ∉ S.biUnion id := (Finset.mem_sdiff.1 hu).2
    have hunion : S.biUnion id ∩ G.neighborFinset u
        = S.biUnion (fun s => s ∩ G.neighborFinset u) := by
      rw [Finset.biUnion_inter]
      simp only [id_eq]
    rw [hunion]
    calc (S.biUnion fun s => s ∩ G.neighborFinset u).card
        ≤ ∑ B ∈ S, (B ∩ G.neighborFinset u).card := Finset.card_biUnion_le
      _ ≤ ∑ _B ∈ S, 2 := Finset.sum_le_sum fun B hB => hclean u hu' B hB
      _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- Therefore each `u ∈ U` has at least `2 * (k - S.card)` neighbours in `U`.
  have hUdeg : ∀ u ∈ U, 2 * (k - S.card) ≤ (G.neighborFinset u ∩ U).card := by
    intro u hu
    have hsub : G.neighborFinset u
        ⊆ (G.neighborFinset u ∩ U) ∪ (S.biUnion id ∩ G.neighborFinset u) := by
      intro w hw
      by_cases hwB : w ∈ S.biUnion id
      · exact Finset.mem_union.2 (Or.inr (Finset.mem_inter.2 ⟨hwB, hw⟩))
      · exact Finset.mem_union.2 (Or.inl (Finset.mem_inter.2
          ⟨hw, Finset.mem_sdiff.2 ⟨Finset.mem_univ w, hwB⟩⟩))
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (G.neighborFinset u ∩ U)
      (S.biUnion id ∩ G.neighborFinset u)
    have hdeg : 2 * k ≤ (G.neighborFinset u).card :=
      hmin.trans (G.minDegree_le_degree u)
    have hle' := hle u hu
    omega
  -- The induced subgraph on `U` has minimum degree at least `2 * (k - S.card)`.
  have hGUmin : 2 * (k - S.card) ≤ (G.induce (↑U : Set V)).minDegree := by
    refine (G.induce (↑U : Set V)).le_minDegree_of_forall_le_degree _ fun v => ?_
    have hvU : (v : V) ∈ U := Finset.mem_coe.1 v.2
    have hmap := congrArg Finset.card (G.map_neighborFinset_induce v)
    rw [Finset.card_map, Finset.toFinset_coe] at hmap
    have hdeg : (G.induce (↑U : Set V)).degree v
        = (G.neighborFinset (v : V) ∩ U).card := hmap
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
      obtain ⟨v0⟩ := hU0
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
  -- `Q` is disjoint from every block of `S`, hence `Q ∉ S`.
  have hQdisj : ∀ B ∈ S, Disjoint Q B := fun B hB =>
    Finset.disjoint_left.2 fun x hxQ hxB =>
      (Finset.mem_sdiff.1 (hQU hxQ)).2 (Finset.mem_biUnion.2 ⟨B, hB, hxB⟩)
  have hQnotMem : Q ∉ S := by
    intro hQS
    obtain ⟨x, hx⟩ : Q.Nonempty := Finset.card_pos.1 (by have hc := hQblk.1; omega)
    exact (Finset.mem_sdiff.1 (hQU hx)).2 (Finset.mem_biUnion.2 ⟨Q, hQS, hx⟩)
  -- `insert Q S` is a larger quadrilateral packing.
  refine ⟨insert Q S, ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hQblk
    · exact hblk t ht
  · intro t₁ h₁ t₂ h₂ hne
    rcases Finset.mem_insert.1 h₁ with rfl | h₁
    · rcases Finset.mem_insert.1 h₂ with rfl | h₂
      · exact absurd rfl hne
      · exact hQdisj t₂ h₂
    · rcases Finset.mem_insert.1 h₂ with rfl | h₂
      · exact (hQdisj t₁ h₁).symm
      · exact hpair t₁ h₁ t₂ h₂ hne
  · rw [Finset.card_insert_of_notMem hQnotMem]
    exact Nat.lt_succ_self S.card

end SimpleGraph
