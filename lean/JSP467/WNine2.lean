import JSP467.WNine
import JSP467.TwoHeavy
import JSP467.CommonNbr

/-!
# JSP-000467 — mixed quads and the nine-edge dichotomy

Second tranche of the `[U, B]` frontier analysis (see `WNine.lean`).
When `U`, `B` are disjoint 4-sets, `B` a quadrilateral block, and
`crossEdges G U B ≥ 9`, either the cross-edge mass concentrates on a unique
*seer* of `B` (a vertex seeing three or all four vertices of `B`), or two
distinct vertices of `U` each see ≥ 3 vertices of `B` — in which case they
share two common neighbours `x, y ∈ B` and `Q = {u₁, x, u₂, y}` is a
*mixed* quadrilateral block meeting `B` in exactly two vertices.  Under the
no-two-disjoint-blocks hypothesis `hnc`, the complementary set
`(U ∪ B) \ Q` cannot itself be a quadrilateral block.

## Main results

* `exists_mixed_quad_of_two_seers` — the mixed quad `{u₁, x, u₂, y}`.
* `mixed_quad_complement_not_quad` — `hnc` forbids its complement to be a
  block.
* `nine_edges_dichotomy` — from `crossEdges ≥ 9`: either two seers, or a
  unique three-seer with all others seeing exactly two, or a unique
  four-seer leaving ≥ 5 residual cross edges.
* `nine_edges_mixed_or_seer` — combined corollary under `hnc`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

/-- **Mixed quad from two seers.**  If two distinct vertices `u₁, u₂` of
`U` each have at least three neighbours inside the disjoint 4-set `B`, they
share two common neighbours `x ≠ y ∈ B`, and `Q = {u₁, x, u₂, y}` is a
quadrilateral block inside `U ∪ B` meeting `B` in exactly the two vertices
`x, y`. -/
theorem exists_mixed_quad_of_two_seers {U B : Finset V} (hU : U.card = 4)
    (hB : B.card = 4) (hdUB : Disjoint U B) {u₁ u₂ : V}
    (hu₁ : u₁ ∈ U) (hu₂ : u₂ ∈ U) (hne : u₁ ≠ u₂)
    (h3₁ : 3 ≤ (B ∩ G.neighborFinset u₁).card)
    (h3₂ : 3 ≤ (B ∩ G.neighborFinset u₂).card) :
    ∃ Q ⊆ U ∪ B, G.IsQuadBlock Q ∧ u₁ ∈ Q ∧ u₂ ∈ Q ∧ (Q ∩ B).card = 2 := by
  obtain ⟨x, hxB, y, hyB, hxy, e1x, e2x, e1y, e2y⟩ :=
    exists_two_common_nbrs_of_two_heavy hB h3₁ h3₂
  have hu₁x : u₁ ≠ x := fun h => Finset.disjoint_left.1 hdUB hu₁ (h ▸ hxB)
  have hu₁y : u₁ ≠ y := fun h => Finset.disjoint_left.1 hdUB hu₁ (h ▸ hyB)
  have hu₂x : u₂ ≠ x := fun h => Finset.disjoint_left.1 hdUB hu₂ (h ▸ hxB)
  have hu₂y : u₂ ≠ y := fun h => Finset.disjoint_left.1 hdUB hu₂ (h ▸ hyB)
  have hu₁B : u₁ ∉ B := fun h => Finset.disjoint_left.1 hdUB hu₁ h
  have hu₂B : u₂ ∉ B := fun h => Finset.disjoint_left.1 hdUB hu₂ h
  refine ⟨{u₁, x, u₂, y}, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Finset.mem_union_left B hu₁
    · exact Finset.mem_union_right U hxB
    · exact Finset.mem_union_left B hu₂
    · exact Finset.mem_union_right U hyB
  · -- Cycle `u₁ - x - u₂ - y - u₁`.
    exact isQuadBlock_of_bip hne hxy hu₁x hu₁y hu₂x hu₂y
      e1x e2x.symm e2y e1y.symm
  · exact Finset.mem_insert_self u₁ _
  · exact Finset.mem_insert.2 (Or.inr (Finset.mem_insert.2
      (Or.inr (Finset.mem_insert_self u₂ _))))
  · have hsub : ({u₁, x, u₂, y} : Finset V) ∩ B ⊆ {x, y} := by
      intro z hz
      obtain ⟨hzQ, hzB⟩ := Finset.mem_inter.1 hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzQ
      rcases hzQ with hz1 | hzx | hz2 | hzy
      · rw [hz1] at hzB
        exact absurd hzB hu₁B
      · rw [hzx]
        exact Finset.mem_insert_self x _
      · rw [hz2] at hzB
        exact absurd hzB hu₂B
      · rw [hzy]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
    have hsup : {x, y} ⊆ ({u₁, x, u₂, y} : Finset V) ∩ B := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hzx | hzy
      · rw [hzx]
        exact Finset.mem_inter.2
          ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self x _), hxB⟩
      · rw [hzy]
        exact Finset.mem_inter.2
          ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))), hyB⟩
    rw [Finset.Subset.antisymm hsub hsup, Finset.card_pair hxy]

/-- **Complement of a sub-quad is not a quad.**  Under the hypothesis `hnc`
that `U ∪ B` contains no two vertex-disjoint quadrilateral blocks, any
quadrilateral block `Q ⊆ U ∪ B` has a non-quadrilateral complement
`(U ∪ B) \ Q`: the two would be disjoint blocks inside `U ∪ B`. -/
theorem mixed_quad_complement_not_quad {U B Q : Finset V}
    (hdUB : Disjoint U B) (hU : U.card = 4) (hB : B.card = 4)
    (hQsub : Q ⊆ U ∪ B) (hQ : G.IsQuadBlock Q)
    (hnc : ¬ ∃ Q₁ Q₂ : Finset V, G.IsQuadBlock Q₁ ∧ G.IsQuadBlock Q₂ ∧
      Disjoint Q₁ Q₂ ∧ Q₁ ∪ Q₂ ⊆ U ∪ B) :
    ¬ G.IsQuadBlock ((U ∪ B) \ Q) := by
  intro hQ2
  have hcover : Q ∪ (U ∪ B) \ Q ⊆ U ∪ B := by
    rw [Finset.union_sdiff_of_subset hQsub]
  exact hnc ⟨Q, (U ∪ B) \ Q, hQ, hQ2, Finset.sdiff_disjoint.symm, hcover⟩

/-- **Nine-edge dichotomy.**  A 4-set `U` sending ≥ 9 edges into a 4-set
`B` either has two distinct *seers* (each seeing ≥ 3 vertices of `B`), or a
unique seer `u`; in the latter case either `u` sees exactly 3 and every
other vertex of `U` sees exactly 2, or `u` sees all 4 and the remaining
three vertices still send ≥ 5 cross edges into `B`. -/
theorem nine_edges_dichotomy {U B : Finset V} (hU : U.card = 4)
    (hB : B.card = 4) (h9 : 9 ≤ crossEdges G U B) :
    (∃ u₁ u₂ : V, u₁ ∈ U ∧ u₂ ∈ U ∧ u₁ ≠ u₂ ∧
        3 ≤ (B ∩ G.neighborFinset u₁).card ∧
        3 ≤ (B ∩ G.neighborFinset u₂).card) ∨
      (∃ u ∈ U, (B ∩ G.neighborFinset u).card = 3 ∧
        ∀ u' ∈ U.erase u, (B ∩ G.neighborFinset u').card = 2) ∨
      (∃ u ∈ U, (B ∩ G.neighborFinset u).card = 4 ∧
        5 ≤ crossEdges G (U.erase u) B) := by
  classical
  by_cases ha : ∃ u₁ u₂ : V, u₁ ∈ U ∧ u₂ ∈ U ∧ u₁ ≠ u₂ ∧
      3 ≤ (B ∩ G.neighborFinset u₁).card ∧
      3 ≤ (B ∩ G.neighborFinset u₂).card
  · exact Or.inl ha
  · obtain ⟨u, hu, hu3⟩ := exists_heavy_of_nine hU h9
    have hle4 : ∀ v ∈ U, (B ∩ G.neighborFinset v).card ≤ 4 := by
      intro v _
      rw [← hB]
      exact Finset.card_le_card Finset.inter_subset_left
    -- Since (a) fails, every vertex of `U` other than `u` sees at most 2.
    have hothers : ∀ u' ∈ U.erase u,
        (B ∩ G.neighborFinset u').card ≤ 2 := by
      intro u' hu'
      obtain ⟨hne', hu'U⟩ := Finset.mem_erase.1 hu'
      by_contra hcon
      exact ha ⟨u, u', hu, hu'U, hne'.symm, hu3, by omega⟩
    have hcard : (U.erase u).card = 3 := by
      rw [Finset.card_erase_of_mem hu, hU]
    have hsum : (B ∩ G.neighborFinset u).card +
        ∑ u' ∈ U.erase u, (B ∩ G.neighborFinset u').card
          = crossEdges G U B :=
      Finset.add_sum_erase U (fun v => (B ∩ G.neighborFinset v).card) hu
    have huc : (B ∩ G.neighborFinset u).card = 3 ∨
        (B ∩ G.neighborFinset u).card = 4 := by
      have h4 := hle4 u hu
      omega
    rcases huc with h3 | h4
    · -- Unique three-seer: the other three each see exactly two.
      refine Or.inr (Or.inl ⟨u, hu, h3, ?_⟩)
      intro u' hu'
      have hle2 := hothers u' hu'
      have hsum' : (B ∩ G.neighborFinset u').card +
          ∑ w ∈ (U.erase u).erase u', (B ∩ G.neighborFinset w).card
            = ∑ w ∈ U.erase u, (B ∩ G.neighborFinset w).card :=
        Finset.add_sum_erase (U.erase u)
          (fun w => (B ∩ G.neighborFinset w).card) hu'
      have hcard' : ((U.erase u).erase u').card = 2 := by
        rw [Finset.card_erase_of_mem hu', hcard]
      have hrest : ∑ w ∈ (U.erase u).erase u',
          (B ∩ G.neighborFinset w).card ≤ 4 := by
        calc ∑ w ∈ (U.erase u).erase u', (B ∩ G.neighborFinset w).card
            ≤ ∑ _w ∈ (U.erase u).erase u', 2 :=
              Finset.sum_le_sum fun w hw =>
                hothers w (Finset.mem_of_mem_erase hw)
          _ = ((U.erase u).erase u').card * 2 := by
              rw [Finset.sum_const, smul_eq_mul]
          _ = 4 := by rw [hcard']
      have h6 : 6 ≤ ∑ w ∈ U.erase u,
          (B ∩ G.neighborFinset w).card := by omega
      omega
    · -- Unique four-seer: the residual sum is at least five.
      refine Or.inr (Or.inr ⟨u, hu, h4, ?_⟩)
      show 5 ≤ ∑ u' ∈ U.erase u, (B ∩ G.neighborFinset u').card
      omega

/-- **Dichotomy under the no-two-blocks hypothesis.**  Combining the
dichotomy with the mixed-quad construction: either two seers yield a mixed
quadrilateral block `Q` (meeting `B` in exactly two vertices, and whose
complement in `U ∪ B` is not a block), or the cross-edge mass concentrates
on a unique seer as in `nine_edges_dichotomy`. -/
theorem nine_edges_mixed_or_seer {U B : Finset V} (hdUB : Disjoint U B)
    (hU : U.card = 4) (hB : B.card = 4) (hBq : G.IsQuadBlock B)
    (hnc : ¬ ∃ Q₁ Q₂ : Finset V, G.IsQuadBlock Q₁ ∧ G.IsQuadBlock Q₂ ∧
      Disjoint Q₁ Q₂ ∧ Q₁ ∪ Q₂ ⊆ U ∪ B)
    (h9 : 9 ≤ crossEdges G U B) :
    (∃ u₁ u₂ : V, u₁ ∈ U ∧ u₂ ∈ U ∧ u₁ ≠ u₂ ∧
        ∃ Q ⊆ U ∪ B, G.IsQuadBlock Q ∧ u₁ ∈ Q ∧ u₂ ∈ Q ∧
          (Q ∩ B).card = 2 ∧ ¬ G.IsQuadBlock ((U ∪ B) \ Q)) ∨
      (∃ u ∈ U, (B ∩ G.neighborFinset u).card = 3 ∧
        ∀ u' ∈ U.erase u, (B ∩ G.neighborFinset u').card = 2) ∨
      (∃ u ∈ U, (B ∩ G.neighborFinset u).card = 4 ∧
        5 ≤ crossEdges G (U.erase u) B) := by
  rcases nine_edges_dichotomy hU hB h9 with h | h | h
  · obtain ⟨u₁, u₂, h1, h2, hne, h3a, h3b⟩ := h
    obtain ⟨Q, hQsub, hQq, hm1, hm2, hcard⟩ :=
      exists_mixed_quad_of_two_seers hU hB hdUB h1 h2 hne h3a h3b
    exact Or.inl ⟨u₁, u₂, h1, h2, hne, Q, hQsub, hQq, hm1, hm2, hcard,
      mixed_quad_complement_not_quad hdUB hU hB hQsub hQq hnc⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end SimpleGraph
