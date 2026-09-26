import JSP467.HoleMove

/-!
# JSP-000467 — unified hole-migration bookkeeping

This module packages the "hole relocation" steps of Wang's switching
argument (Wa10) into reusable existence statements.  At a lexicographically
maximal non-covering packing `S` under the hypothesis `hnolarger` (no
strictly larger quadrilateral packing exists), a low-leftover-degree vertex
`u` that is *heavy* on a block `B ∈ S` (≥ 3 neighbours inside `B`) can be
absorbed into the packing: exchanging `u` for a freeable `w₁ ∈ B` and
rotating `w₁` back (`exists_rotate_back`) yields a same-cardinality packing
`S₂` whose covered set is `(∪S).erase w₂ ∪ {u}` — the uncovered "hole" has
migrated from `u` to a covered vertex `w₂`, while `u` is absorbed and
`blockSum` does not increase.

* `exists_hole_relocate` — the unified one-step relocation: `u` absorbed,
  the hole lands at some `w₂ ∈ ∪S`, `∪S₂ = (∪S).erase w₂ ∪ {u}`.
* `exists_hole_relocate_iter` — the relocation composed twice: the next
  low-leftover-degree heavy vertex `u₂` of `S₂` (supplied inside
  `exists_rotate_back` by `exists_heavy_lowdeg_of_no_larger`, since
  `hnolarger` and the cardinality bound transfer across equal-cardinality
  packings) is in turn exchanged for a freeable `w₃` of its heavy block
  `B₂ ∈ S₂`.  The net covered set is
  `((∪S).erase w₂ ∪ {u}).erase w₃ ∪ {u₂}` and the leftover is
  `((univ \ ∪S).erase u ∪ {w₂}).erase u₂ ∪ {w₃}`; if `u₂ = w₂` or `w₃ = u`
  the hole simply returns towards `∪S`, which is exactly what the formulas
  record.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Unified hole relocation.**  At a lex-max non-covering packing under
`hnolarger`, the heavy leftover vertex `u` is absorbed and the hole lands
at some previously covered vertex `w₂ ∈ ∪S`: there is a packing `S₂` of the
same cardinality covering `(∪S).erase w₂ ∪ {u}` with
`blockSum G S₂ ≤ blockSum G S`. -/
theorem exists_hole_relocate (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) (hlt : S.card < k)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    (hnolarger : ¬ ∃ T : Finset (Finset V),
      G.IsQuadPacking T ∧ S.card < T.card)
    {u : V} (hu : u ∈ Finset.univ \ S.biUnion id)
    (hudeg : ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card
      ≤ 2 * (k - S.card) - 1)
    {B : Finset V} (hB : B ∈ S)
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    ∃ w₂ : V, ∃ S₂ : Finset (Finset V),
      w₂ ∈ S.biUnion id ∧ w₂ ≠ u ∧
      G.IsQuadPacking S₂ ∧ S₂.card = S.card ∧
      S₂.biUnion id = (S.biUnion id).erase w₂ ∪ {u} ∧
      blockSum G S₂ ≤ blockSum G S := by
  classical
  have hu' : u ∉ S.biUnion id := (Finset.mem_sdiff.1 hu).2
  have huB : u ∉ B := fun h => hu' (Finset.subset_biUnion_of_mem id hB h)
  -- Any freeable vertex `w₁ ∈ B` works: the heavy-back condition is
  -- automatic at a lex-max packing (`freed_heavy_back_of_lexmax`).
  obtain ⟨w₁, _, hw₁B, -, -, hBw₁, _⟩ :=
    exists_two_freeable (hS.1 B hB) huB h3
  obtain ⟨w₂, S₂, _u₂, _B₂, _hw₂B, hw₂X, hw₂u, hP₂, hC₂, hX₂, _hUb₂, hbs,
    _hrot, _hheavy₂, _hu₂U, _hdeg₂, _hB₂S₂, _h3₂⟩ :=
    exists_rotate_back G k hcard hmin hS hlt hlex hnolarger hu hudeg hB hw₁B
      hBw₁ h3
  exact ⟨w₂, S₂, hw₂X, hw₂u, hP₂, hC₂, hX₂, hbs⟩

/-- **Relocation composed twice.**  After the first relocation moves the
hole from `u` to `w₂` (packing `S₂`), `hnolarger` and the cardinality bound
transfer to `S₂`, so the dichotomy produces the next low-leftover-degree
heavy vertex `u₂` with a heavy block `B₂ ∈ S₂`.  A plain exchange then
absorbs `u₂` in place of a freeable `w₃ ∈ B₂`: the net covered set is
`((∪S).erase w₂ ∪ {u}).erase w₃ ∪ {u₂}` and the new leftover is
`((univ \ ∪S).erase u ∪ {w₂}).erase u₂ ∪ {w₃}`.  (If `u₂ = w₂` or `w₃ = u`
the hole simply moves back inside `∪S`; the formulas record the honest
result in all cases.) -/
theorem exists_hole_relocate_iter (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) (hlt : S.card < k)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    (hnolarger : ¬ ∃ T : Finset (Finset V),
      G.IsQuadPacking T ∧ S.card < T.card)
    {u : V} (hu : u ∈ Finset.univ \ S.biUnion id)
    (hudeg : ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card
      ≤ 2 * (k - S.card) - 1)
    {B : Finset V} (hB : B ∈ S)
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    ∃ (w₂ w₃ u₂ : V) (S₂ S₃ : Finset (Finset V)),
      w₂ ∈ S.biUnion id ∧ w₂ ≠ u ∧
      G.IsQuadPacking S₂ ∧ S₂.card = S.card ∧
      S₂.biUnion id = (S.biUnion id).erase w₂ ∪ {u} ∧
      Finset.univ \ S₂.biUnion id =
        (Finset.univ \ S.biUnion id).erase u ∪ {w₂} ∧
      blockSum G S₂ ≤ blockSum G S ∧
      u₂ ∈ Finset.univ \ S₂.biUnion id ∧
      ((Finset.univ \ S₂.biUnion id) ∩ G.neighborFinset u₂).card
        ≤ 2 * (k - S.card) - 1 ∧
      w₃ ∈ S₂.biUnion id ∧ w₃ ≠ u₂ ∧
      G.IsQuadPacking S₃ ∧ S₃.card = S.card ∧
      S₃.biUnion id = ((S.biUnion id).erase w₂ ∪ {u}).erase w₃ ∪ {u₂} ∧
      Finset.univ \ S₃.biUnion id =
        ((Finset.univ \ S.biUnion id).erase u ∪ {w₂}).erase u₂ ∪ {w₃} ∧
      blockSum G S₃ ≤ blockSum G S := by
  classical
  have hu' : u ∉ S.biUnion id := (Finset.mem_sdiff.1 hu).2
  have huB : u ∉ B := fun h => hu' (Finset.subset_biUnion_of_mem id hB h)
  -- First relocation: absorb `u`, the hole lands at `w₂`.
  obtain ⟨w₁, _, hw₁B, -, -, hBw₁, _⟩ :=
    exists_two_freeable (hS.1 B hB) huB h3
  obtain ⟨w₂, S₂, u₂, B₂, _hw₂B, hw₂X, hw₂u, hP₂, hC₂, hX₂, hUb₂, hbs,
    _hrot, _hheavy₂, hu₂U, hdeg₂, hB₂S₂, h3₂⟩ :=
    exists_rotate_back G k hcard hmin hS hlt hlex hnolarger hu hudeg hB hw₁B
      hBw₁ h3
  -- Second relocation: `u₂` is heavy on `B₂ ∈ S₂`; exchange `u₂` for a
  -- freeable `w₃ ∈ B₂` (a plain exchange suffices — no lex-max needed).
  have hu₂' : u₂ ∉ S₂.biUnion id := (Finset.mem_sdiff.1 hu₂U).2
  have hu₂B₂ : u₂ ∉ B₂ :=
    fun h => hu₂' (Finset.subset_biUnion_of_mem id hB₂S₂ h)
  obtain ⟨w₃, _, hw₃B₂, -, -, hBw₃, _⟩ :=
    exists_two_freeable (hP₂.1 B₂ hB₂S₂) hu₂B₂ h3₂
  have hw₃X : w₃ ∈ S₂.biUnion id :=
    Finset.subset_biUnion_of_mem id hB₂S₂ hw₃B₂
  have hw₃u₂ : w₃ ≠ u₂ := fun h => hu₂' (h ▸ hw₃X)
  obtain ⟨hP₃, hC₃, hX₃⟩ := hP₂.exchange_block hu₂' hB₂S₂ hw₃B₂ hBw₃
  set S₃ := insert (insert u₂ (B₂.erase w₃)) (S₂.erase B₂) with _hS₃def
  -- Cardinality, covering equation and leftover equation of `S₃`.
  have hC₃S : S₃.card = S.card := hC₃.trans hC₂
  have hX₃S : S₃.biUnion id
      = ((S.biUnion id).erase w₂ ∪ {u}).erase w₃ ∪ {u₂} := by
    rw [hX₃, hX₂]
  have hUb₃ : Finset.univ \ S₃.biUnion id
      = ((Finset.univ \ S.biUnion id).erase u ∪ {w₂}).erase u₂ ∪ {w₃} := by
    have h : Finset.univ \ S₃.biUnion id
        = (Finset.univ \ S₂.biUnion id).erase u₂ ∪ {w₃} := by
      rw [hX₃]
      exact univ_sdiff_erase_union_singleton hw₃X hu₂'
    rw [h, hUb₂]
  -- `blockSum` does not increase: `hlex` applies to `S₃` (same card).
  have hbs₃ : blockSum G S₃ ≤ blockSum G S := by
    rcases hlex S₃ hP₃ hC₃S with hlt' | ⟨heq, -⟩
    · exact le_of_lt hlt'
    · exact le_of_eq heq
  exact ⟨w₂, w₃, u₂, S₂, S₃, hw₂X, hw₂u, hP₂, hC₂, hX₂, hUb₂, hbs, hu₂U,
    hdeg₂, hw₃X, hw₃u₂, hP₃, hC₃S, hX₃S, hUb₃, hbs₃⟩

end SimpleGraph
