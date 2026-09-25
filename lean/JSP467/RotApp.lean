import JSP467.Rotate
import JSP467.Exchange

/-!
# JSP-000467 — packaged rotation bounds for downstream use

This module packages the exchange + rotation steps of Wang's argument into
ready-to-use existence statements:

* `univ_sdiff_erase_union_singleton` — set algebra for the leftover after an
  exchange `u ↔ w` (`w` covered, `u` uncovered):
  `univ \ ((∪S).erase w ∪ {u}) = (univ \ ∪S).erase u ∪ {w}`.
* `exists_exchange_rotBound` — for an `edgeSum`-maximal packing `S`, an
  uncovered `u` with ≥ 3 neighbours in a block `B` can be exchanged for some
  `w ∈ B`, and `w`'s neighbourhood in the reduced leftover is no larger than
  `u`'s was.
* `exists_two_exchange_rotBound` — the two-witness refinement via
  `exists_two_freeable`: two distinct `w₁, w₂ ∈ B` are simultaneously
  freeable, and *every* freeable `w ∈ B` satisfies the rotation bound.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Set algebra for the exchange: if `w ∈ X` and `u ∉ X`, then
`univ \ (X.erase w ∪ {u}) = (univ \ X).erase u ∪ {w}`. -/
theorem univ_sdiff_erase_union_singleton {X : Finset V} {u w : V}
    (hw : w ∈ X) (hu : u ∉ X) :
    Finset.univ \ (X.erase w ∪ {u})
      = (Finset.univ \ X).erase u ∪ {w} := by
  have hne : w ≠ u := fun h => hu (h ▸ hw)
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_erase,
    Finset.mem_union, Finset.mem_singleton, true_and]
  constructor
  · intro hx
    by_cases hxw : x = w
    · exact Or.inr hxw
    · exact Or.inl ⟨fun hxu => hx (Or.inr hxu),
        fun hxX => hx (Or.inl ⟨hxw, hxX⟩)⟩
  · intro hx
    rcases hx with ⟨hxu, hxX⟩ | rfl
    · rintro (⟨-, hxX'⟩ | h)
      · exact hxX hxX'
      · exact hxu h
    · rintro (⟨hww, -⟩ | h)
      · exact hww rfl
      · exact absurd h hne

/-- Packaged rotation: for an `edgeSum`-maximal packing `S`, an uncovered `u`
with ≥ 3 neighbours in block `B` can be exchanged for some `w ∈ B`, and `w`'s
neighbourhood in the reduced leftover is no larger than `u`'s was. -/
theorem exists_exchange_rotBound [DecidableRel G.Adj] {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S)
    (hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      edgeSum G (Finset.univ \ T.biUnion id) ≤
        edgeSum G (Finset.univ \ S.biUnion id))
    {u : V} (hu : u ∈ Finset.univ \ S.biUnion id) {B : Finset V} (hB : B ∈ S)
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    ∃ w ∈ B, ∃ S' : Finset (Finset V), G.IsQuadPacking S' ∧ S'.card = S.card ∧
      Finset.univ \ S'.biUnion id =
        (Finset.univ \ S.biUnion id).erase u ∪ {w} ∧
      ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card ≤
        ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card := by
  have hu' : u ∉ S.biUnion id := (Finset.mem_sdiff.1 hu).2
  obtain ⟨w, hwB, S', hS', hcard, hUb⟩ :=
    exists_exchange_packing hS hu' hB h3
  have hwU : w ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB hwB
  have hcov : Finset.univ \ S'.biUnion id
      = (Finset.univ \ S.biUnion id).erase u ∪ {w} := by
    rw [hUb]
    exact univ_sdiff_erase_union_singleton hwU hu'
  exact ⟨w, hwB, S', hS', hcard, hcov,
    rotate_neighbor_card_le hmax hu hwU hS' hcard hcov⟩

/-- Two-witness rotation bound.  If `S` is `edgeSum`-maximal and the
uncovered `u` is heavy on `B` (≥ 3 neighbours), then there are two distinct
freeable vertices `w₁, w₂ ∈ B` (each making `insert u (B.erase wᵢ)` a
quadrilateral block), and *every* freeable `w ∈ B` satisfies the rotation
bound: `w`'s degree into the reduced leftover is at most `u`'s leftover
degree. -/
theorem exists_two_exchange_rotBound [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      edgeSum G (Finset.univ \ T.biUnion id) ≤
        edgeSum G (Finset.univ \ S.biUnion id))
    {u : V} (hu : u ∈ Finset.univ \ S.biUnion id) {B : Finset V} (hB : B ∈ S)
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    ∃ w₁ w₂ : V, w₁ ∈ B ∧ w₂ ∈ B ∧ w₁ ≠ w₂ ∧
      (∀ {w : V} (_ : w ∈ B) (_ : G.IsQuadBlock (insert u (B.erase w))),
        ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card ≤
          ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card) ∧
      G.IsQuadBlock (insert u (B.erase w₁)) ∧
      G.IsQuadBlock (insert u (B.erase w₂)) := by
  have hu' : u ∉ S.biUnion id := (Finset.mem_sdiff.1 hu).2
  have huB : u ∉ B := fun h => hu' (Finset.subset_biUnion_of_mem id hB h)
  -- The bound holds for every freeable `w ∈ B`, via `exchange_block` to get
  -- the exchanged packing and `rotate_neighbor_card_le` for the inequality.
  have hbound : ∀ {w : V} (_ : w ∈ B)
      (_ : G.IsQuadBlock (insert u (B.erase w))),
      ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card ≤
        ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card := by
    intro w hwB hBw
    obtain ⟨hS', hcard, hUb⟩ := hS.exchange_block hu' hB hwB hBw
    have hwU : w ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB hwB
    have hcov : Finset.univ \ (insert (insert u (B.erase w))
        (S.erase B)).biUnion id
        = (Finset.univ \ S.biUnion id).erase u ∪ {w} := by
      rw [hUb]
      exact univ_sdiff_erase_union_singleton hwU hu'
    exact rotate_neighbor_card_le hmax hu hwU hS' hcard hcov
  obtain ⟨w₁, w₂, hw₁B, hw₂B, hne, hq₁, hq₂⟩ :=
    exists_two_freeable (hS.1 B hB) huB h3
  exact ⟨w₁, w₂, hw₁B, hw₂B, hne, hbound, hq₁, hq₂⟩

end SimpleGraph
