import JSP467.Pairing
import JSP467.Exchange
import Mathlib.Data.Fin.VecNotation

/-!
# JSP-000467 — heavy-vertex exchange lemmas

When a vertex `v` outside a quadrilateral block `s` is adjacent to *every*
vertex of `s`, every vertex `w ∈ s` is freeable: `insert v (s.erase w)` is
again a quadrilateral block.  This strengthens `IsQuadBlock.exchange`
(which requires only three neighbours) for the "heavy" case of Wang's
argument.

* `IsQuadBlock.exchange_all` — every vertex of the block is freeable.
* `exists_exchange_all` — the packing-level corollary via
  `IsQuadPacking.exchange_block`.
* `card_four_subset_neighbor_of_full` — cardinality test for full
  adjacency.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- If `v ∉ s` is adjacent to all four vertices of a quadrilateral block `s`,
then every `w ∈ s` can be swapped for `v`: writing `w = x i` in the cycle
order `x` of the copy of `C₄`, the new cycle is
`v - x(i+1) - x(i+2) - x(i+3) - v`. -/
theorem IsQuadBlock.exchange_all [DecidableRel G.Adj] {s : Finset V} {v : V}
    (hs : G.IsQuadBlock s) (hv : v ∉ s) (hadj : ∀ x ∈ s, G.Adj v x) :
    ∀ w ∈ s, G.IsQuadBlock (insert v (s.erase w)) := by
  obtain ⟨hc, ⟨f⟩⟩ := hs
  -- Arithmetic facts about `Fin 4`, used to rotate the cycle order.
  have hU : ∀ j : Fin 4,
      (Finset.univ : Finset (Fin 4)) = {j, j + 1, j + 2, j + 3} := by
    intro j; fin_cases j <;> decide
  have hne : ∀ j : Fin 4, j + 1 ≠ j ∧ j + 2 ≠ j ∧ j + 3 ≠ j
      ∧ j + 1 ≠ j + 2 ∧ j + 1 ≠ j + 3 ∧ j + 2 ≠ j + 3 := by
    intro j; fin_cases j <;> decide
  have hcA : ∀ j : Fin 4, (cycleGraph 4).Adj (j + 1) (j + 2) := by
    intro j; fin_cases j <;> decide
  have hcB : ∀ j : Fin 4, (cycleGraph 4).Adj (j + 2) (j + 3) := by
    intro j; fin_cases j <;> decide
  -- The 4-cycle order on `s` coming from the copy of `C₄`.
  set x : Fin 4 → V := fun i => (f i).1 with hx_def
  have hxs : ∀ i : Fin 4, x i ∈ s := fun i => Finset.mem_coe.1 (f i).2
  have hinj : Function.Injective x := fun i j h => f.injective (Subtype.ext h)
  have hcyc : ∀ i j : Fin 4, (cycleGraph 4).Adj i j → G.Adj (x i) (x j) :=
    fun i j h => induce_adj.1 (f.toHom.map_adj h)
  have hs_img : s = Finset.univ.image x := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · rw [Finset.image_subset_iff]
      exact fun i _ => hxs i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
        Fintype.card_fin]
      omega
  intro w hw
  -- Write `w = x i` for some cycle index `i`.
  rw [hs_img] at hw
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
  have hne' := hne i
  have hs4 : s = {x i, x (i + 1), x (i + 2), x (i + 3)} := by
    rw [hs_img, hU i]
    simp [Finset.image_insert, Finset.image_singleton]
  have hset : insert v (s.erase (x i))
      = {v, x (i + 1), x (i + 2), x (i + 3)} := by
    rw [hs4]
    ext w
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro (rfl | ⟨hwx, rfl | rfl | rfl | rfl⟩)
      · exact Or.inl rfl
      · exact absurd rfl hwx
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨fun h => hne'.1 (hinj h), Or.inr (Or.inl rfl)⟩
      · exact Or.inr ⟨fun h => hne'.2.1 (hinj h), Or.inr (Or.inr (Or.inl rfl))⟩
      · exact Or.inr ⟨fun h => hne'.2.2.1 (hinj h),
          Or.inr (Or.inr (Or.inr rfl))⟩
  have hvne : ∀ i : Fin 4, v ≠ x i := fun i h => hv (h.symm ▸ hxs i)
  exact IsQuadBlock.of_cycle hset
    (hvne (i + 1)) (hvne (i + 2)) (hvne (i + 3))
    (hinj.ne hne'.2.2.2.1) (hinj.ne hne'.2.2.2.2.1) (hinj.ne hne'.2.2.2.2.2)
    (hadj _ (hxs (i + 1))) (hcyc _ _ (hcA i)) (hcyc _ _ (hcB i))
    (hadj _ (hxs (i + 3))).symm

/-- A leftover vertex `u` adjacent to all of a packing block `B` can be
exchanged into `B` at *any* position `w ∈ B`, producing a packing of the
same cardinality covering `(∪S).erase w ∪ {u}`. -/
theorem exists_exchange_all [DecidableRel G.Adj] {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S) {u : V} (hu : u ∉ S.biUnion id) {B : Finset V}
    (hB : B ∈ S) (hadj : ∀ x ∈ B, G.Adj u x) (w : V) (hw : w ∈ B) :
    ∃ S' : Finset (Finset V), G.IsQuadPacking S' ∧ S'.card = S.card ∧
      S'.biUnion id = (S.biUnion id).erase w ∪ {u} := by
  have huB : u ∉ B := fun h => hu (Finset.subset_biUnion_of_mem id hB h)
  obtain ⟨hp, hc, hU⟩ := hS.exchange_block hu hB hw
    (IsQuadBlock.exchange_all (hS.1 B hB) huB hadj w hw)
  exact ⟨_, hp, hc, hU⟩

/-- Cardinality test for full adjacency: if a 4-element set `B` has four
neighbours of `u` inside it, then `u` is adjacent to every vertex of `B`. -/
theorem card_four_subset_neighbor_of_full [DecidableRel G.Adj]
    {B : Finset V} {u : V}
    (hB : B.card = 4) (h4 : (B ∩ G.neighborFinset u).card = 4) :
    ∀ x ∈ B, G.Adj u x := by
  have hcard_eq : (B ∩ G.neighborFinset u).card = B.card := by rw [h4, hB]
  have heq : B ∩ G.neighborFinset u = B :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard_eq.ge
  intro x hx
  have hx' : x ∈ B ∩ G.neighborFinset u := by rw [heq]; exact hx
  exact (G.mem_neighborFinset u x).1 (Finset.mem_inter.1 hx').2

end SimpleGraph
