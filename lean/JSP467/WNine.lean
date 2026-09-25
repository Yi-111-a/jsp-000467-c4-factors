import JSP467.WCount
import JSP467.WCover
import JSP467.Heavy
import JSP467.Chord

/-!
# JSP-000467 — the `[U, B]` frontier with nine cross-edges

The counting finish of Wang (Wa10) reduces to a local analysis on a
4-vertex leftover `U` and a single quadrilateral block `B` of the packing
with `crossEdges G U B ≥ 9`, under the hypothesis that `U ∪ B` contains no
two vertex-disjoint quadrilateral blocks (otherwise the packing enlarges via
`exists_larger_of_two_blocks`).

This module proves the first structural slivers of that analysis:

* `exists_heavy_of_nine` — pigeonhole: some `u ∈ U` has at least three
  neighbours inside `B`.
* `two_blocks_extend` — the swap `u ↔ w` partitions `U ∪ B` into the two
  candidate blocks `insert u (B.erase w)` and `(U.erase u) ∪ {w}`.
* `no2C4_leftover_quadfree` — if `w` is freeable for `u`, the new leftover
  `(U.erase u) ∪ {w}` cannot itself be a quadrilateral block.
* `exists_freeable_pair_quadfree` — a heavy `u` yields *two* freeable
  vertices of `B`, each with a non-quadrilateral leftover.
* `k4_of_full_seer` — under `blockSum`-maximality of the cover, a leftover
  vertex adjacent to all of `B` forces `B` to span `K₄`
  (`edgeSum G B = 12`).

All statements are over an ambient `SimpleGraph V` with
`[DecidableRel G.Adj]`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

/-- **Pigeonhole.**  If the four vertices of `U` send at least nine edges
into `B`, some `u ∈ U` sees at least three vertices of `B`. -/
theorem exists_heavy_of_nine {U B : Finset V} (hU : U.card = 4)
    (h9 : 9 ≤ crossEdges G U B) :
    ∃ u ∈ U, 3 ≤ (B ∩ G.neighborFinset u).card := by
  by_contra hcon
  push Not at hcon
  have hle : crossEdges G U B ≤ U.card * 2 := by
    unfold crossEdges
    calc ∑ u ∈ U, (B ∩ G.neighborFinset u).card
        ≤ ∑ _u ∈ U, 2 :=
          Finset.sum_le_sum fun u hu => by have h := hcon u hu; omega
      _ = U.card * 2 := by rw [Finset.sum_const, smul_eq_mul]
  rw [hU] at hle
  omega

omit [Fintype V] in
/-- **Swap partition.**  For `u ∈ U` and `w ∈ B` with `U`, `B` disjoint, the
candidate swapped block `insert u (B.erase w)` and the candidate new
leftover `(U.erase u) ∪ {w}` are disjoint and together sit inside `U ∪ B`
(in fact they partition it). -/
theorem two_blocks_extend {U B : Finset V} (hdUB : Disjoint U B) {u w : V}
    (hu : u ∈ U) (hw : w ∈ B) :
    Disjoint (insert u (B.erase w)) (U.erase u ∪ {w}) ∧
      insert u (B.erase w) ∪ (U.erase u ∪ {w}) ⊆ U ∪ B := by
  have huw : u ≠ w := fun h =>
    Finset.disjoint_left.1 hdUB hu (h ▸ hw)
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx hx2
    rcases Finset.mem_insert.1 hx with rfl | hxB
    · rcases Finset.mem_union.1 hx2 with hxU | hxw
      · exact (Finset.mem_erase.1 hxU).1 rfl
      · exact huw (Finset.mem_singleton.1 hxw)
    · obtain ⟨hxne, hxB'⟩ := Finset.mem_erase.1 hxB
      rcases Finset.mem_union.1 hx2 with hxU | hxs
      · exact Finset.disjoint_left.1 hdUB (Finset.mem_of_mem_erase hxU) hxB'
      · exact hxne (Finset.mem_singleton.1 hxs)
  · refine Finset.union_subset ?_ ?_
    · intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hxB
      · exact Finset.mem_union_left B hu
      · exact Finset.mem_union_right U (Finset.mem_of_mem_erase hxB)
    · refine Finset.union_subset ?_ ?_
      · intro x hx
        exact Finset.mem_union_left B (Finset.mem_of_mem_erase hx)
      · exact Finset.singleton_subset_iff.2 (Finset.mem_union_right U hw)

omit [Fintype V] [DecidableRel G.Adj] in
/-- **No-two-quads restriction.**  If `w ∈ B` is freeable for `u ∈ U` (the
swap `insert u (B.erase w)` is again a quadrilateral block), then the
complementary new leftover `(U.erase u) ∪ {w}` cannot be a quadrilateral
block: the two would be disjoint quadrilateral blocks inside `U ∪ B`. -/
theorem no2C4_leftover_quadfree {U B : Finset V} (hdUB : Disjoint U B)
    (hnc : ¬ ∃ Q₁ Q₂ : Finset V, G.IsQuadBlock Q₁ ∧ G.IsQuadBlock Q₂ ∧
      Disjoint Q₁ Q₂ ∧ Q₁ ∪ Q₂ ⊆ U ∪ B)
    {u w : V} (hu : u ∈ U) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert u (B.erase w))) :
    ¬ G.IsQuadBlock (U.erase u ∪ {w}) := by
  intro hQ
  exact hnc ⟨insert u (B.erase w), U.erase u ∪ {w}, hBw, hQ,
    (two_blocks_extend hdUB hu hw).1, (two_blocks_extend hdUB hu hw).2⟩

/-- A heavy leftover vertex yields *two* freeable vertices of `B`
(`exists_two_freeable`), and for each of them the new leftover is not a
quadrilateral block. -/
theorem exists_freeable_pair_quadfree {U B : Finset V} (hdUB : Disjoint U B)
    (hBq : G.IsQuadBlock B)
    (hnc : ¬ ∃ Q₁ Q₂ : Finset V, G.IsQuadBlock Q₁ ∧ G.IsQuadBlock Q₂ ∧
      Disjoint Q₁ Q₂ ∧ Q₁ ∪ Q₂ ⊆ U ∪ B)
    {u : V} (hu : u ∈ U)
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    ∃ w₁ w₂ : V, w₁ ∈ B ∧ w₂ ∈ B ∧ w₁ ≠ w₂ ∧
      ¬ G.IsQuadBlock (U.erase u ∪ {w₁}) ∧
      ¬ G.IsQuadBlock (U.erase u ∪ {w₂}) := by
  have huB : u ∉ B := fun h => Finset.disjoint_left.1 hdUB hu h
  obtain ⟨w₁, w₂, hw₁, hw₂, hne, hq₁, hq₂⟩ :=
    exists_two_freeable hBq huB h3
  exact ⟨w₁, w₂, hw₁, hw₂, hne,
    no2C4_leftover_quadfree hdUB hnc hu hw₁ hq₁,
    no2C4_leftover_quadfree hdUB hnc hu hw₂ hq₂⟩

/-- **Full seer ⇒ `K₄`.**  In a `blockSum`-maximal cover `(S, U)`, if the
leftover vertex `u` is adjacent to all four vertices of the packing block
`B`, then every `w ∈ B` is universal inside `B`, so `B` spans `K₄`:
`edgeSum G B = 12`. -/
theorem k4_of_full_seer {S : Finset (Finset V)} {U B : Finset V} {u : V}
    (hc : G.IsCover S U)
    (hmax : ∀ S' : Finset (Finset V), G.IsQuadPacking S' → S'.card = S.card →
      blockSum G S' ≤ blockSum G S)
    (hB : B ∈ S) (hu : u ∈ U)
    (h4 : (B ∩ G.neighborFinset u).card = 4) :
    edgeSum G B = 12 := by
  have hBq : G.IsQuadBlock B := hc.hS.1 B hB
  have hBcard : B.card = 4 := hBq.1
  have huUB : u ∉ S.biUnion id := fun h =>
    Finset.disjoint_left.1 hc.hdisj h hu
  have huB : u ∉ B := fun h =>
    huUB (Finset.subset_biUnion_of_mem id hB h)
  have hadj : ∀ x ∈ B, G.Adj u x :=
    card_four_subset_neighbor_of_full hBcard h4
  -- Every `w ∈ B` is freeable (`u` sees all of `B`), hence universal in `B`.
  have huniv : ∀ w ∈ B, ∀ x ∈ B, x ≠ w → G.Adj w x := by
    intro w hw
    exact freeable_universal_of_full hc.hS hmax huUB hB hw
      (IsQuadBlock.exchange_all hBq huB hadj w hw) hadj
  -- Each vertex of `B` has exactly the other three vertices as neighbours
  -- inside `B`.
  have hterm : ∀ w ∈ B, (B ∩ G.neighborFinset w).card = 3 := by
    intro w hw
    have hset : B ∩ G.neighborFinset w = B.erase w := by
      ext x
      simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_erase]
      constructor
      · rintro ⟨hxB, hxa⟩
        exact ⟨(G.ne_of_adj hxa).symm, hxB⟩
      · rintro ⟨hxw, hxB⟩
        exact ⟨hxB, huniv w hw x hxB hxw⟩
    rw [hset, Finset.card_erase_of_mem hw, hBcard]
  calc edgeSum G B = ∑ _w ∈ B, 3 := Finset.sum_congr rfl hterm
    _ = 12 := by rw [Finset.sum_const, smul_eq_mul, hBcard]

/-- If `u` sees exactly three of the four vertices of the quadrilateral
block `B`, missing `b0`, then its neighbourhood inside `B` is exactly
`B.erase b0`. -/
theorem three_seer_eq_erase {B : Finset V} (hBq : G.IsQuadBlock B)
    {u b0 : V} (hb0 : b0 ∈ B) (hnadj : ¬ G.Adj u b0)
    (h3 : (B ∩ G.neighborFinset u).card = 3) :
    B ∩ G.neighborFinset u = B.erase b0 := by
  have hsub : B ∩ G.neighborFinset u ⊆ B.erase b0 := by
    intro x hx
    obtain ⟨hxB, hxn⟩ := Finset.mem_inter.1 hx
    rw [G.mem_neighborFinset] at hxn
    exact Finset.mem_erase.2 ⟨fun h => hnadj (h ▸ hxn), hxB⟩
  have hc : (B.erase b0).card = 3 := by
    rw [Finset.card_erase_of_mem hb0, hBq.1]
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

/-- `blockSum`-maximal variant of `freeable_universal_of_full`: if `u` sees
all three remaining vertices `B.erase w` of a freeable `w`, then `w` is
universal inside `B`. -/
theorem freeable_universal_of_three {S : Finset (Finset V)} {u w : V}
    {B : Finset V} (hS : G.IsQuadPacking S)
    (hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T ≤ blockSum G S)
    (hu : u ∉ S.biUnion id) (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert u (B.erase w)))
    (h3 : (B.erase w ∩ G.neighborFinset u).card = 3) :
    ∀ x ∈ B, x ≠ w → G.Adj w x := by
  have hle := blockSum_exchange_le hS hmax hu hB hw hBw
  have hBcard : B.card = 4 := (hS.1 B hB).1
  have herase : (B.erase w).card = 3 := by
    rw [Finset.card_erase_of_mem hw, hBcard]
  rw [h3] at hle
  have heq : B.erase w ∩ G.neighborFinset w = B.erase w :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [herase]; exact hle)
  intro x hx hxw
  have hxn : x ∈ B.erase w ∩ G.neighborFinset w := by
    rw [heq]; exact Finset.mem_erase.2 ⟨hxw, hx⟩
  exact (G.mem_neighborFinset w x).1 (Finset.mem_inter.1 hxn).2

/-- **Three-seer restriction at the missed vertex.**  In a
`blockSum`-maximal cover, if `u ∈ U` sees exactly three vertices of `B`,
missing `b0`, and the missed vertex `b0` itself is freeable, then `b0` is
universal inside `B` and the new leftover `(U.erase u) ∪ {b0}` is not a
quadrilateral block. -/
theorem three_seer_missed_vertex {S : Finset (Finset V)} {U B : Finset V}
    {u b0 : V}
    (hc : G.IsCover S U)
    (hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T ≤ blockSum G S)
    (hnc : ¬ ∃ Q₁ Q₂ : Finset V, G.IsQuadBlock Q₁ ∧ G.IsQuadBlock Q₂ ∧
      Disjoint Q₁ Q₂ ∧ Q₁ ∪ Q₂ ⊆ U ∪ B)
    (hB : B ∈ S) (hu : u ∈ U) (hb0 : b0 ∈ B) (hnadj : ¬ G.Adj u b0)
    (h3 : (B ∩ G.neighborFinset u).card = 3)
    (hB0 : G.IsQuadBlock (insert u (B.erase b0))) :
    (∀ x ∈ B, x ≠ b0 → G.Adj b0 x) ∧
      ¬ G.IsQuadBlock (U.erase u ∪ {b0}) := by
  have hBq : G.IsQuadBlock B := hc.hS.1 B hB
  have huUB : u ∉ S.biUnion id := fun h =>
    Finset.disjoint_left.1 hc.hdisj h hu
  have hdUB : Disjoint U B := Finset.disjoint_of_subset_right
    (Finset.subset_biUnion_of_mem id hB) hc.hdisj.symm
  have hcap : B.erase b0 ∩ G.neighborFinset u
      = B ∩ G.neighborFinset u := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase, G.mem_neighborFinset]
    constructor
    · rintro ⟨⟨-, hxB⟩, hxu⟩
      exact ⟨hxB, hxu⟩
    · rintro ⟨hxB, hxu⟩
      exact ⟨⟨fun h => hnadj (h ▸ hxu), hxB⟩, hxu⟩
  refine ⟨freeable_universal_of_three hc.hS hmax huUB hB hb0 hB0 ?_, ?_⟩
  · rw [hcap, h3]
  · exact no2C4_leftover_quadfree hdUB hnc hu hb0 hB0

/-- **Three-seer restriction at a non-missed vertex.**  Same setting: a
freeable `w ≠ b0` sees only two of `u`'s neighbours in `B`, so
`blockSum`-maximality forces `w` to have at least two neighbours inside
`B`, and again the new leftover is not a quadrilateral block. -/
theorem three_seer_nonmissed_vertex {S : Finset (Finset V)} {U B : Finset V}
    {u w b0 : V}
    (hc : G.IsCover S U)
    (hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T ≤ blockSum G S)
    (hnc : ¬ ∃ Q₁ Q₂ : Finset V, G.IsQuadBlock Q₁ ∧ G.IsQuadBlock Q₂ ∧
      Disjoint Q₁ Q₂ ∧ Q₁ ∪ Q₂ ⊆ U ∪ B)
    (hB : B ∈ S) (hu : u ∈ U) (hb0 : b0 ∈ B) (hnadj : ¬ G.Adj u b0)
    (h3 : (B ∩ G.neighborFinset u).card = 3)
    (hw : w ∈ B) (hwb0 : w ≠ b0)
    (hBw : G.IsQuadBlock (insert u (B.erase w))) :
    2 ≤ (B.erase w ∩ G.neighborFinset w).card ∧
      ¬ G.IsQuadBlock (U.erase u ∪ {w}) := by
  have hBq : G.IsQuadBlock B := hc.hS.1 B hB
  have hBcard : B.card = 4 := hBq.1
  have huUB : u ∉ S.biUnion id := fun h =>
    Finset.disjoint_left.1 hc.hdisj h hu
  have hdUB : Disjoint U B := Finset.disjoint_of_subset_right
    (Finset.subset_biUnion_of_mem id hB) hc.hdisj.symm
  have hBsub : B ∩ G.neighborFinset u = B.erase b0 :=
    three_seer_eq_erase hBq hb0 hnadj h3
  have hcap : B.erase w ∩ G.neighborFinset u
      = (B ∩ G.neighborFinset u).erase w := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase]
    tauto
  have h2 : (B.erase w ∩ G.neighborFinset u).card = 2 := by
    rw [hcap, hBsub,
      Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hwb0, hw⟩),
      Finset.card_erase_of_mem hb0, hBcard]
  have hle := blockSum_exchange_le hc.hS hmax huUB hB hw hBw
  exact ⟨by omega, no2C4_leftover_quadfree hdUB hnc hu hw hBw⟩

end SimpleGraph
