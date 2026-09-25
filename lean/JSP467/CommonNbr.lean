import JSP467.K4Case
import JSP467.Exchange

/-!
# JSP-000467 — common-neighbour characterisation of quadrilateral blocks

A finite simple graph contains a `C₄` on a 4-element vertex set `s` iff some
pair of distinct vertices of `s` has at least two common neighbours inside
`s` (the two antipodal vertices of the cycle share the other two).  This file
packages that equivalence together with its packing-level consequences:

* `IsQuadBlock.exists_cycle` — extract a cyclic order `a - x - b - y - a`
  spanning `s` from a quadrilateral block `s`.
* `IsQuadBlock.two_common` — the antipodal pair of the cycle has two common
  neighbours inside the block.
* `exists_quadBlock_of_two_common` — a pair `a ≠ b` in `U` with two common
  neighbours inside `U` yields a quadrilateral block `{a, x, b, y} ⊆ U`.
* `IsQuadBlock.iff_two_common` — the `C₄`-inside-`s` ↔ two-common-neighbours
  equivalence for 4-element `s`.
* `no_quadBlock_iff_common_le_one` — a finset is quad-block-free iff every
  pair of distinct vertices inside it has at most one common neighbour.
* `exists_larger_of_two_common_leftover` — two common neighbours in the
  leftover vertices enlarge a quadrilateral packing.
* `exists_larger_of_freed_common` — after an exchange `u ↔ w`, two common
  neighbours of `w` and a leftover vertex inside the new leftover set
  enlarge the packing.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Extract the cyclic order `a - x - b - y - a` of a quadrilateral block:
`s = {a, x, b, y}` with the four consecutive cycle adjacencies. -/
theorem IsQuadBlock.exists_cycle {s : Finset V} (hs : G.IsQuadBlock s) :
    ∃ a b x y : V, s = {a, x, b, y} ∧ a ≠ b ∧ x ≠ y ∧
      G.Adj a x ∧ G.Adj x b ∧ G.Adj b y ∧ G.Adj y a := by
  obtain ⟨hc, ⟨f⟩⟩ := hs
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
  have hU0 : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  have hs4 : s = {x 0, x 1, x 2, x 3} := by
    rw [hs_img, hU0]
    simp [Finset.image_insert, Finset.image_singleton]
  -- Antipodal pair `x 0, x 2` with common neighbours `x 1, x 3`.
  exact ⟨x 0, x 2, x 1, x 3, hs4,
    hinj.ne (by decide), hinj.ne (by decide),
    hcyc _ _ (by decide), hcyc _ _ (by decide),
    hcyc _ _ (by decide), hcyc _ _ (by decide)⟩

/-- In a quadrilateral block, the two antipodal vertices of its `C₄` share
the other two vertices as common neighbours inside the block. -/
theorem IsQuadBlock.two_common [DecidableRel G.Adj] {s : Finset V}
    (hs : G.IsQuadBlock s) :
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧
      2 ≤ (s ∩ G.neighborFinset a ∩ G.neighborFinset b).card := by
  obtain ⟨a, b, x, y, hs4, hab, hxy, e_ax, e_xb, e_by, e_ya⟩ := hs.exists_cycle
  have has : a ∈ s := by simp [hs4]
  have hbs : b ∈ s := by simp [hs4]
  have hxs : x ∈ s := by simp [hs4]
  have hys : y ∈ s := by simp [hs4]
  refine ⟨a, has, b, hbs, hab, ?_⟩
  have hsub : ({x, y} : Finset V) ⊆
      s ∩ G.neighborFinset a ∩ G.neighborFinset b := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_inter.2 ⟨Finset.mem_inter.2
        ⟨hxs, (G.mem_neighborFinset a x).2 e_ax⟩,
        (G.mem_neighborFinset b x).2 e_xb.symm⟩
    · exact Finset.mem_inter.2 ⟨Finset.mem_inter.2
        ⟨hys, (G.mem_neighborFinset a y).2 e_ya.symm⟩,
        (G.mem_neighborFinset b y).2 e_by⟩
  rw [← Finset.card_pair hxy]
  exact Finset.card_le_card hsub

/-- A pair of distinct vertices `a, b ∈ U` with at least two common
neighbours inside `U` yields a quadrilateral block `{a, x, b, y} ⊆ U`:
the cycle `a - x - b - y - a`. -/
theorem exists_quadBlock_of_two_common [DecidableRel G.Adj] {U : Finset V}
    {a b : V} (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b)
    (h2 : 2 ≤ (U ∩ G.neighborFinset a ∩ G.neighborFinset b).card) :
    ∃ Q : Finset V, Q ⊆ U ∧ G.IsQuadBlock Q := by
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    Finset.one_lt_card.1
      (show 1 < (U ∩ G.neighborFinset a ∩ G.neighborFinset b).card by omega)
  have hxU : x ∈ U := (Finset.mem_inter.1 (Finset.mem_inter.1 hx).1).1
  have hyU : y ∈ U := (Finset.mem_inter.1 (Finset.mem_inter.1 hy).1).1
  have hax : G.Adj a x := (G.mem_neighborFinset a x).1
    (Finset.mem_inter.1 (Finset.mem_inter.1 hx).1).2
  have hbx : G.Adj b x :=
    (G.mem_neighborFinset b x).1 (Finset.mem_inter.1 hx).2
  have hay : G.Adj a y := (G.mem_neighborFinset a y).1
    (Finset.mem_inter.1 (Finset.mem_inter.1 hy).1).2
  have hby : G.Adj b y :=
    (G.mem_neighborFinset b y).1 (Finset.mem_inter.1 hy).2
  refine ⟨{a, x, b, y}, ?_, isQuadBlock_of_bip hab hxy hax.ne hay.ne hbx.ne
    hby.ne hax hbx.symm hby hay.symm⟩
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ha
  · exact hxU
  · exact hb
  · exact hyU

/-- For a 4-element set `s`, being a quadrilateral block is equivalent to
containing a pair of distinct vertices with two common neighbours in `s`. -/
theorem IsQuadBlock.iff_two_common [DecidableRel G.Adj] {s : Finset V}
    (hsc : s.card = 4) :
    G.IsQuadBlock s ↔ ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧
      2 ≤ (s ∩ G.neighborFinset a ∩ G.neighborFinset b).card := by
  constructor
  · exact fun h => h.two_common
  · rintro ⟨a, ha, b, hb, hab, h2⟩
    obtain ⟨Q, hQs, hQ⟩ := exists_quadBlock_of_two_common ha hb hab h2
    have hQs' : Q = s :=
      Finset.eq_of_subset_of_card_le hQs (by rw [hQ.1]; omega)
    exact hQs' ▸ hQ

/-- A finset `U` contains no quadrilateral block iff every pair of distinct
vertices of `U` has at most one common neighbour inside `U`. -/
theorem no_quadBlock_iff_common_le_one [DecidableRel G.Adj] {U : Finset V} :
    (∀ Q : Finset V, Q ⊆ U → ¬ G.IsQuadBlock Q) ↔
      ∀ a ∈ U, ∀ b ∈ U, a ≠ b →
        (U ∩ G.neighborFinset a ∩ G.neighborFinset b).card ≤ 1 := by
  constructor
  · -- Two common neighbours inside `U` would produce a quad block in `U`.
    intro hU a ha b hb hab
    by_contra hle
    obtain ⟨Q, hQU, hQ⟩ :=
      exists_quadBlock_of_two_common ha hb hab (by omega)
    exact hU Q hQU hQ
  · -- A quad block inside `U` would give a pair with two common neighbours.
    intro hle Q hQU hQb
    obtain ⟨a, haQ, b, hbQ, hab, h2⟩ := hQb.two_common
    have hsub : Q ∩ G.neighborFinset a ∩ G.neighborFinset b ⊆
        U ∩ G.neighborFinset a ∩ G.neighborFinset b := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.1 hx
      obtain ⟨hxQ, hxa⟩ := Finset.mem_inter.1 hx1
      exact Finset.mem_inter.2
        ⟨Finset.mem_inter.2 ⟨hQU hxQ, hxa⟩, hx2⟩
    have h2' : 2 ≤ (U ∩ G.neighborFinset a ∩ G.neighborFinset b).card :=
      le_trans h2 (Finset.card_le_card hsub)
    have h1 := hle a (hQU haQ) b (hQU hbQ) hab
    omega

/-- Enlargement via the common-neighbour test: if two distinct leftover
vertices `a, b` share two common neighbours inside the leftover set
`univ \ ⋃S`, the quadrilateral packing `S` can be enlarged. -/
theorem exists_larger_of_two_common_leftover [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) {a b : V}
    (ha : a ∈ Finset.univ \ S.biUnion id)
    (hb : b ∈ Finset.univ \ S.biUnion id) (hab : a ≠ b)
    (h2 : 2 ≤ ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset a
      ∩ G.neighborFinset b).card) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  obtain ⟨Q, hQU, hQ⟩ := exists_quadBlock_of_two_common ha hb hab h2
  exact exists_larger_of_leftover_block hS hQ hQU

/-- Enlargement after an exchange: swapping `u` (leftover, heavy on `B`) for
`w ∈ B` gives the packing `S'` with leftover
`U' = (univ \ ⋃S).erase u ∪ {w}`.  If `w` and some `a ∈ U' \ {w}` share two
common neighbours inside `U'`, then `U'` contains a quadrilateral block and
`S` (via `S'`) can be enlarged. -/
theorem exists_larger_of_freed_common [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) {u w : V} {B : Finset V}
    (hu : u ∉ S.biUnion id) (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert u (B.erase w)))
    {a : V} (hwa : w ≠ a)
    (ha : a ∈ (Finset.univ \ S.biUnion id).erase u ∪ {w})
    (h2 : 2 ≤ (((Finset.univ \ S.biUnion id).erase u ∪ {w})
      ∩ G.neighborFinset w ∩ G.neighborFinset a).card) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  have hwU : w ∈ (Finset.univ \ S.biUnion id).erase u ∪ {w} :=
    Finset.mem_union.2 (Or.inr (Finset.mem_singleton_self w))
  obtain ⟨Q, hQU, hQ⟩ := exists_quadBlock_of_two_common hwU ha hwa h2
  exact exists_larger_of_exchange_leftover_block hS hu hB hw hBw hQ hQU

end SimpleGraph
