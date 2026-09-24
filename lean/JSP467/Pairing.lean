import JSP467.Defs
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Pairing and exchange lemmas for quadrilateral blocks

Reusable lemmas for the Wang (Wa10) formalization:

* `IsQuadBlock.of_edge_pair` — two vertex-disjoint edges `a-b`, `c-d` with
  the parallel cross edges `a-c`, `b-d` span a quadrilateral block.
* `IsQuadBlock.exchange` — if `v ∉ s` has at least three neighbours inside a
  quadrilateral block `s`, then some `w ∈ s` can be swapped for `v`.
* `exists_block_ge_degree` — pigeonhole over a family of disjoint blocks:
  if `v` has more than `m * (r - 1)` neighbours inside the union of `m`
  pairwise-disjoint sets, some part contains at least `r` neighbours of `v`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Two vertex-disjoint edges `a-b` and `c-d` with the parallel cross edges
`a-c` and `b-d` span a quadrilateral block (`a-b-d-c-a` is a 4-cycle). -/
theorem IsQuadBlock.of_edge_pair {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d)
    (e_ab : G.Adj a b) (e_cd : G.Adj c d) (e_ac : G.Adj a c) (e_bd : G.Adj b d) :
    G.IsQuadBlock {a, b, c, d} := by
  have hs : ({a, b, c, d} : Finset V) = {a, b, d, c} := by
    rw [Finset.pair_comm c d]
  exact IsQuadBlock.of_cycle hs hab had hac hbd hbc hcd.symm
    e_ab e_bd e_cd.symm e_ac.symm

/-- Exchange lemma: if `s` is a quadrilateral block and `v ∉ s` has at least 3
neighbors in `s`, then some vertex `w ∈ s` can be swapped for `v`: the set
`insert v (s.erase w)` is again a quadrilateral block. -/
theorem IsQuadBlock.exchange [DecidableRel G.Adj] {s : Finset V} {v : V}
    (hs : G.IsQuadBlock s) (hv : v ∉ s)
    (h3 : 3 ≤ (s ∩ G.neighborFinset v).card) :
    ∃ w ∈ s, G.IsQuadBlock (insert v (s.erase w)) := by
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
  -- Indices of non-neighbours of `v` among the four cycle vertices:
  -- there is at most one.
  set B : Finset (Fin 4) :=
    Finset.univ.filter (fun i => ¬ G.Adj v (x i)) with hB_def
  have hBsub : B.image x ⊆ s \ (s ∩ G.neighborFinset v) := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    rw [hB_def, Finset.mem_filter] at hi
    rw [Finset.mem_sdiff]
    refine ⟨hxs i, fun h => hi.2 ?_⟩
    rw [Finset.mem_inter] at h
    exact (G.mem_neighborFinset v _).1 h.2
  have hBcard : B.card ≤ 1 := by
    have h1 := Finset.card_le_card hBsub
    rw [Finset.card_image_of_injective _ hinj,
      Finset.card_sdiff_of_subset Finset.inter_subset_left, hc] at h1
    omega
  -- Pick `j` such that every other cycle vertex is a neighbour of `v`.
  obtain ⟨j, hj⟩ : ∃ j : Fin 4, B ⊆ {j} := by
    by_cases hB0 : B = ∅
    · exact ⟨0, hB0 ▸ Finset.empty_subset _⟩
    · obtain ⟨j, hj⟩ := Finset.nonempty_of_ne_empty hB0
      exact ⟨j, fun i hi =>
        Finset.mem_singleton.2 (Finset.card_le_one.1 hBcard i hi j hj)⟩
  rw [hB_def] at hj
  have hNB : ∀ i : Fin 4, i ≠ j → G.Adj v (x i) := by
    intro i hi
    by_contra hna
    exact hi (Finset.mem_singleton.1
      (hj (Finset.mem_filter.2 ⟨Finset.mem_univ i, hna⟩)))
  -- Rebuild the block with `v` replacing `x j`: the new cycle is
  -- `v - x(j+1) - x(j+2) - x(j+3) - v`.
  refine ⟨x j, hxs j, ?_⟩
  have hne' := hne j
  have hs4 : s = {x j, x (j + 1), x (j + 2), x (j + 3)} := by
    rw [hs_img, hU j]
    simp [Finset.image_insert, Finset.image_singleton]
  have hset : insert v (s.erase (x j))
      = {v, x (j + 1), x (j + 2), x (j + 3)} := by
    rw [hs4]
    ext w
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    tauto
  have hvne : ∀ i : Fin 4, v ≠ x i := fun i h => hv (h.symm ▸ hxs i)
  exact IsQuadBlock.of_cycle hset
    (hvne (j + 1)) (hvne (j + 2)) (hvne (j + 3))
    (hinj.ne hne'.2.2.2.1) (hinj.ne hne'.2.2.2.2.1) (hinj.ne hne'.2.2.2.2.2)
    (hNB (j + 1) hne'.1) (hcyc _ _ (hcA j)) (hcyc _ _ (hcB j))
    (hNB (j + 3) hne'.2.2.1).symm

/-- Pigeonhole over a disjoint family: if `v` has more than `m * (r - 1)`
neighbours inside the union of `m` pairwise-disjoint sets, then some part
contains at least `r` neighbours of `v`. -/
theorem exists_block_ge_degree [DecidableRel G.Adj] {S : Finset (Finset V)}
    {v : V} {r : ℕ}
    (hpair : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s t)
    (h : S.card * (r - 1) < ((S.biUnion id) ∩ G.neighborFinset v).card) :
    ∃ s ∈ S, r ≤ (s ∩ G.neighborFinset v).card := by
  have hunion : (S.biUnion id) ∩ G.neighborFinset v
      = S.biUnion (fun s => s ∩ G.neighborFinset v) := by
    rw [Finset.biUnion_inter]
    simp only [id_eq]
  have hdisj : (S : Set (Finset V)).PairwiseDisjoint
      (fun s => s ∩ G.neighborFinset v) :=
    fun s hs t ht hne =>
      Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
        (hpair s hs t ht hne)
  rw [hunion, Finset.card_biUnion hdisj] at h
  by_contra hcon
  push_neg at hcon
  have hle : ∑ s ∈ S, (s ∩ G.neighborFinset v).card ≤ S.card * (r - 1) := by
    calc ∑ s ∈ S, (s ∩ G.neighborFinset v).card
        ≤ ∑ _s ∈ S, (r - 1) :=
          Finset.sum_le_sum fun s hs => by have hlt := hcon s hs; omega
      _ = S.card * (r - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
  omega

end SimpleGraph
