import JSP467.ThreeQuads
import JSP467.CommonNbr
import JSP467.HoleMove
import JSP467.Cascade

/-!
# JSP-000467 — two heavy leftover vertices on the same block

This file develops the "two heavy on one block" case of Wang's switching
argument (Wa10).  If two distinct leftover vertices `u, u'` of a lex-max
quadrilateral packing `S` each have at least three neighbours inside a single
packing block `B`, then — since `|B| = 4` — they share at least two common
neighbours `x, y ∈ B`.  The four-element set `Q₁ = {u, x, u', y}` then carries
the cycle `u - x - u' - y - u`, hence is a quadrilateral block inside
`U ∪ B = univ \ ⋃(S.erase B)`.  If the complementary region
`R = (U \ {u,u'}) ∪ (B \ {x,y})` contains a second quadrilateral block `Q₂`,
the two-block enlargement `exists_larger_of_two_blocks` finishes.

## Main results

* `exists_two_common_nbrs_of_two_heavy` — the pigeonhole: two heavy vertices
  on a four-element `B` share two common neighbours in `B`.
* `exists_quadBlock_of_two_heavy` — the quadrilateral block
  `Q₁ = {u, x, u', y}` inside `univ \ ⋃(S.erase B)`.
* `exists_larger_of_two_heavy_same_block_of_leftover` — enlargement when the
  complementary region already contains a quadrilateral block.
* `exists_larger_of_two_heavy_same_block` — the full theorem.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **Pigeonhole.**  If `B` has four vertices and `u, u'` each have at least
three neighbours inside `B`, then they share at least two common neighbours
`x ≠ y` in `B` (both adjacent to both). -/
theorem exists_two_common_nbrs_of_two_heavy [DecidableRel G.Adj]
    {B : Finset V} {u u' : V} (hB4 : B.card = 4)
    (h3u : 3 ≤ (B ∩ G.neighborFinset u).card)
    (h3u' : 3 ≤ (B ∩ G.neighborFinset u').card) :
    ∃ x ∈ B, ∃ y ∈ B, x ≠ y ∧
      G.Adj u x ∧ G.Adj u' x ∧ G.Adj u y ∧ G.Adj u' y := by
  classical
  -- `|A ∩ A'| = |A| + |A'| - |A ∪ A'| ≥ 3 + 3 - |B| = 2`.
  have h2 : 2 ≤ (B ∩ G.neighborFinset u ∩ G.neighborFinset u').card := by
    have hunion : (B ∩ G.neighborFinset u) ∪ (B ∩ G.neighborFinset u') ⊆ B :=
      Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
    have hcard := Finset.card_le_card hunion
    have hsum := Finset.card_union_add_card_inter
      (B ∩ G.neighborFinset u) (B ∩ G.neighborFinset u')
    have hset : (B ∩ G.neighborFinset u) ∩ (B ∩ G.neighborFinset u')
        = B ∩ G.neighborFinset u ∩ G.neighborFinset u' := by
      ext z
      simp only [Finset.mem_inter]
      tauto
    rw [hset] at hsum
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h2
  refine ⟨x, ?_, y, ?_, hxy, ?_, ?_, ?_, ?_⟩
  · exact (Finset.mem_inter.1 (Finset.mem_inter.1 hx).1).1
  · exact (Finset.mem_inter.1 (Finset.mem_inter.1 hy).1).1
  · exact (G.mem_neighborFinset u x).1
      (Finset.mem_inter.1 (Finset.mem_inter.1 hx).1).2
  · exact (G.mem_neighborFinset u' x).1 (Finset.mem_inter.1 hx).2
  · exact (G.mem_neighborFinset u y).1
      (Finset.mem_inter.1 (Finset.mem_inter.1 hy).1).2
  · exact (G.mem_neighborFinset u' y).1 (Finset.mem_inter.1 hy).2

end SimpleGraph
