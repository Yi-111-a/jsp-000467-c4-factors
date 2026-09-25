import JSP467.Main
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fin.VecNotation

/-!
# JSP-000467 — edge-counting rotation machinery for the heavy-vertex case

For a quadrilateral packing `S`, the *leftover* is `univ \ S.biUnion id`.
An *exchange* swaps a leftover vertex `u` into a block in place of `w`,
moving `w` to the leftover: the new leftover is `(U.erase u) ∪ {w}`.

Among packings of the same cardinality one may choose `S` to maximise the
number of edges inside the leftover (`exists_max_edgeSum_packing`).  The
resulting degree-comparison inequality `rotate_neighbor_card_le` says that a
freeable vertex `w` has no more leftover-neighbours (excluding `u`) than `u`
itself had — the key input to the rotation step of Wang's argument.

* `edgeSum` — twice the number of edges of `G` inside a finset.
* `edgeSum_eq_card_filter` — `edgeSum` counts ordered adjacent pairs.
* `edgeSum_insert` / `edgeSum_exchange` — the algebra of the exchange.
* `exists_max_edgeSum_packing` — a maximizer for the leftover edge-sum.
* `rotate_neighbor_card_le` — the rotation inequality.
* `exists_two_freeable` — at least two vertices of a block are freeable when
  an outside vertex sees at least three of them.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Twice the number of edges of `G` inside `U`: the sum over `u ∈ U` of the
number of neighbours of `u` that lie in `U`. -/
def edgeSum (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) : ℕ :=
  ∑ u ∈ U, (U ∩ G.neighborFinset u).card

/-- `edgeSum U` counts ordered pairs of adjacent vertices inside `U`
(each edge is counted once in each direction). -/
theorem edgeSum_eq_card_filter [DecidableRel G.Adj] (U : Finset V) :
    edgeSum G U = ((U ×ˢ U).filter fun p => G.Adj p.1 p.2).card := by
  have h : ∀ x ∈ U, (U ∩ G.neighborFinset x).card
      = ∑ y ∈ U, (if G.Adj x y then 1 else 0) := by
    intro x _
    rw [← Finset.card_filter]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]
  calc edgeSum G U
      = ∑ x ∈ U, ∑ y ∈ U, (if G.Adj x y then 1 else 0) := by
        unfold edgeSum
        exact Finset.sum_congr rfl h
    _ = ((U ×ˢ U).filter fun p => G.Adj p.1 p.2).card := by
        rw [← Finset.sum_product', Finset.card_filter]

/-- Inserting a fresh vertex `a` into `U` raises the edge-sum by twice the
number of neighbours of `a` inside `U`: once for `a`'s own term and once
spread over the terms of its neighbours. -/
theorem edgeSum_insert [DecidableRel G.Adj] (U : Finset V) {a : V}
    (ha : a ∉ U) :
    edgeSum G (insert a U)
      = edgeSum G U + 2 * (U ∩ G.neighborFinset a).card := by
  classical
  have haNa : insert a U ∩ G.neighborFinset a
      = U ∩ G.neighborFinset a := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert, G.mem_neighborFinset]
    constructor
    · rintro ⟨rfl | hx, hadj⟩
      · exact absurd hadj (fun h => G.ne_of_adj h rfl)
      · exact ⟨hx, hadj⟩
    · rintro ⟨hx, hadj⟩
      exact ⟨Or.inr hx, hadj⟩
  have hcard : ∀ x ∈ U, (insert a U ∩ G.neighborFinset x).card
      = (U ∩ G.neighborFinset x).card + (if G.Adj a x then 1 else 0) := by
    intro x hx
    by_cases hax : G.Adj a x
    · have h : insert a U ∩ G.neighborFinset x
          = insert a (U ∩ G.neighborFinset x) := by
        ext y
        simp only [Finset.mem_inter, Finset.mem_insert, G.mem_neighborFinset]
        constructor
        · rintro ⟨rfl | hy, hxy⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hy, hxy⟩
        · rintro (rfl | ⟨hy, hxy⟩)
          · exact ⟨Or.inl rfl, hax.symm⟩
          · exact ⟨Or.inr hy, hxy⟩
      rw [h, Finset.card_insert_of_notMem
        (fun hh => ha (Finset.mem_inter.1 hh).1), if_pos hax]
    · have h : insert a U ∩ G.neighborFinset x
          = U ∩ G.neighborFinset x := by
        ext y
        simp only [Finset.mem_inter, Finset.mem_insert, G.mem_neighborFinset]
        constructor
        · rintro ⟨rfl | hy, hxy⟩
          · exact absurd hxy.symm hax
          · exact ⟨hy, hxy⟩
        · rintro ⟨hy, hxy⟩
          exact ⟨Or.inr hy, hxy⟩
      rw [h, if_neg hax, add_zero]
  have hsum : ∑ x ∈ U, (if G.Adj a x then 1 else 0)
      = (U ∩ G.neighborFinset a).card := by
    rw [← Finset.card_filter]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_inter, G.mem_neighborFinset]
  calc edgeSum G (insert a U)
      = (insert a U ∩ G.neighborFinset a).card
          + ∑ x ∈ U, (insert a U ∩ G.neighborFinset x).card := by
        unfold edgeSum
        exact Finset.sum_insert ha
    _ = (U ∩ G.neighborFinset a).card
          + ∑ x ∈ U, ((U ∩ G.neighborFinset x).card
              + if G.Adj a x then 1 else 0) := by
        rw [haNa]
        congr 1
        exact Finset.sum_congr rfl hcard
    _ = (U ∩ G.neighborFinset a).card
          + (∑ x ∈ U, (U ∩ G.neighborFinset x).card
              + (U ∩ G.neighborFinset a).card) := by
        rw [Finset.sum_add_distrib, hsum]
    _ = edgeSum G U + 2 * (U ∩ G.neighborFinset a).card := by
        unfold edgeSum
        omega

/-- Exchanging `u ∈ U` for `w ∉ U` in the leftover changes the edge-sum by
`-2 * (neighbours of u in U) + 2 * (neighbours of w in U \ {u})`. -/
theorem edgeSum_exchange [DecidableRel G.Adj] (U : Finset V) {u w : V}
    (hu : u ∈ U) (hw : w ∉ U) :
    edgeSum G (U.erase u ∪ {w}) =
      edgeSum G U - 2 * (U ∩ G.neighborFinset u).card
        + 2 * ((U.erase u) ∩ G.neighborFinset w).card := by
  have hwu : w ∉ U.erase u := fun h => hw (Finset.mem_of_mem_erase h)
  have hinter : U.erase u ∩ G.neighborFinset u
      = U ∩ G.neighborFinset u := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase, G.mem_neighborFinset]
    constructor
    · rintro ⟨⟨_, hx⟩, hadj⟩
      exact ⟨hx, hadj⟩
    · rintro ⟨hx, hadj⟩
      refine ⟨⟨?_, hx⟩, hadj⟩
      rintro rfl
      exact G.ne_of_adj hadj rfl
  have hsplit : edgeSum G U
      = edgeSum G (U.erase u) + 2 * (U ∩ G.neighborFinset u).card := by
    conv_lhs => rw [← Finset.insert_erase hu]
    rw [edgeSum_insert (U.erase u) (Finset.notMem_erase u U), hinter]
  have hunion : U.erase u ∪ {w} = insert w (U.erase u) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase,
      Finset.mem_insert]
    tauto
  rw [hunion, edgeSum_insert (U.erase u) hwu, hsplit]
  omega

/-- Among quadrilateral packings of a fixed cardinality `m` there is one
maximising the edge-sum of its leftover. -/
theorem exists_max_edgeSum_packing [DecidableRel G.Adj] (m : ℕ)
    (hne : ∃ S : Finset (Finset V), G.IsQuadPacking S ∧ S.card = m) :
    ∃ S : Finset (Finset V), G.IsQuadPacking S ∧ S.card = m ∧
      ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = m →
        edgeSum G (Finset.univ \ T.biUnion id) ≤
          edgeSum G (Finset.univ \ S.biUnion id) := by
  classical
  set P : Finset (Finset (Finset V)) :=
    univ.filter fun S => G.IsQuadPacking S ∧ S.card = m with hPdef
  have hmem : ∀ S : Finset (Finset V),
      S ∈ P ↔ G.IsQuadPacking S ∧ S.card = m := by
    intro S
    simp [hPdef]
  obtain ⟨S₀, hS₀⟩ := hne
  have hne' : P.Nonempty := ⟨S₀, (hmem S₀).2 hS₀⟩
  obtain ⟨S, hSP, hSmax⟩ := Finset.exists_max_image P
    (fun S => edgeSum G (Finset.univ \ S.biUnion id)) hne'
  exact ⟨S, ((hmem S).1 hSP).1, ((hmem S).1 hSP).2,
    fun T hT hTm => hSmax T ((hmem T).2 ⟨hT, hTm⟩)⟩

/-- **Rotation inequality.**  If `S` maximises the leftover edge-sum among
packings of its cardinality, and exchanging the leftover vertex `u` for the
block vertex `w` produces another packing `S'` of the same cardinality whose
leftover is `(U.erase u) ∪ {w}`, then `w` has at most as many neighbours in
`U \ {u}` as `u` has in `U`. -/
theorem rotate_neighbor_card_le [DecidableRel G.Adj] {S : Finset (Finset V)}
    (hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      edgeSum G (Finset.univ \ T.biUnion id) ≤
        edgeSum G (Finset.univ \ S.biUnion id))
    {u w : V} (hu : u ∈ Finset.univ \ S.biUnion id)
    (hw : w ∈ S.biUnion id) {S' : Finset (Finset V)}
    (hS' : G.IsQuadPacking S') (hcard : S'.card = S.card)
    (hcov : Finset.univ \ S'.biUnion id
      = (Finset.univ \ S.biUnion id).erase u ∪ {w}) :
    ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card ≤
      ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card := by
  set U := Finset.univ \ S.biUnion id with hUdef
  have hwU : w ∉ U := fun h => (Finset.mem_sdiff.1 h).2 hw
  have hle := hmax S' hS' hcard
  rw [hcov, edgeSum_exchange U hu hwU] at hle
  omega

/-- When `v ∉ s` has at least three neighbours inside a quadrilateral block
`s`, at least *two* vertices of `s` can be swapped for `v`: if `j` is a cycle
index covering all non-neighbours of `v`, then both `x j` and its antipode
`x (j + 2)` are freeable. -/
theorem exists_two_freeable [DecidableRel G.Adj] {s : Finset V} {v : V}
    (hs : G.IsQuadBlock s) (hv : v ∉ s)
    (h3 : 3 ≤ (s ∩ G.neighborFinset v).card) :
    ∃ w₁ w₂ : V, w₁ ∈ s ∧ w₂ ∈ s ∧ w₁ ≠ w₂ ∧
      G.IsQuadBlock (insert v (s.erase w₁)) ∧
      G.IsQuadBlock (insert v (s.erase w₂)) := by
  classical
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
  have hcC : ∀ j : Fin 4, (cycleGraph 4).Adj (j + 3) j := by
    intro j; fin_cases j <;> decide
  have hcD : ∀ j : Fin 4, (cycleGraph 4).Adj j (j + 1) := by
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
  have hne' := hne j
  have hs4 : s = {x j, x (j + 1), x (j + 2), x (j + 3)} := by
    rw [hs_img, hU j]
    simp [Finset.image_insert, Finset.image_singleton]
  have hvne : ∀ i : Fin 4, v ≠ x i := fun i h => hv (h.symm ▸ hxs i)
  -- First freeable vertex: `x j`.  The new cycle is
  -- `v - x(j+1) - x(j+2) - x(j+3) - v`.
  have hset1 : insert v (s.erase (x j))
      = {v, x (j + 1), x (j + 2), x (j + 3)} := by
    rw [hs4]
    ext w
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro (rfl | ⟨hwxj, rfl | rfl | rfl | rfl⟩)
      · exact Or.inl rfl
      · exact absurd rfl hwxj
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨fun h => hne'.1 (hinj h), Or.inr (Or.inl rfl)⟩
      · exact Or.inr ⟨fun h => hne'.2.1 (hinj h), Or.inr (Or.inr (Or.inl rfl))⟩
      · exact Or.inr ⟨fun h => hne'.2.2.1 (hinj h),
          Or.inr (Or.inr (Or.inr rfl))⟩
  -- Second freeable vertex: the antipode `x (j + 2)`.  The new cycle is
  -- `v - x(j+3) - x j - x(j+1) - v`.
  have hset2 : insert v (s.erase (x (j + 2)))
      = {v, x (j + 3), x j, x (j + 1)} := by
    rw [hs4]
    ext w
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro (rfl | ⟨hwx, rfl | rfl | rfl | rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact absurd rfl hwx
      · exact Or.inr (Or.inl rfl)
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨fun h => hne'.2.2.2.2.2 (hinj h).symm,
          Or.inr (Or.inr (Or.inr rfl))⟩
      · exact Or.inr ⟨fun h => hne'.2.1 (hinj h).symm, Or.inl rfl⟩
      · exact Or.inr ⟨fun h => hne'.2.2.2.1 (hinj h), Or.inr (Or.inl rfl)⟩
  refine ⟨x j, x (j + 2), hxs j, hxs (j + 2), hinj.ne hne'.2.1.symm, ?_, ?_⟩
  · exact IsQuadBlock.of_cycle hset1 (hvne (j + 1)) (hvne (j + 2)) (hvne (j + 3))
      (hinj.ne hne'.2.2.2.1) (hinj.ne hne'.2.2.2.2.1) (hinj.ne hne'.2.2.2.2.2)
      (hNB (j + 1) hne'.1) (hcyc _ _ (hcA j)) (hcyc _ _ (hcB j))
      (hNB (j + 3) hne'.2.2.1).symm
  · exact IsQuadBlock.of_cycle hset2 (hvne (j + 3)) (hvne j) (hvne (j + 1))
      (hinj.ne hne'.2.2.1) (hinj.ne hne'.2.2.2.2.1.symm)
      (hinj.ne hne'.1.symm)
      (hNB (j + 3) hne'.2.2.1) (hcyc _ _ (hcC j)) (hcyc _ _ (hcD j))
      (hNB (j + 1) hne'.1).symm

end SimpleGraph
