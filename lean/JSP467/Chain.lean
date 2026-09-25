import JSP467.Exchange
import JSP467.Rotate
import JSP467.Pairing

/-!
# JSP-000467 — two-step exchange chains

The core of Wang's switching argument (Wa10): if an uncovered vertex `u` can be
exchanged into a packing block `B₁`, freeing `w₁`, and `w₁` can in turn be
exchanged into a different block `B₂`, freeing `w₂`, then performing both
exchanges yields a packing of the same cardinality whose covered set is
`(∪S).erase w₂ ∪ {u}` — the intermediate freed vertex `w₁` is covered again by
the second exchange.

* `exists_two_step_exchange` — the chained exchange on the covered set.
* `exists_two_step_exchange_leftover` — the same statement phrased on the
  leftover set: `univ \ ∪S'' = (univ \ ∪S).erase u ∪ {w₂}`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **Two-step exchange chain.** If the uncovered vertex `u` can replace `w₁`
in the packing block `B₁` (the swapped set remaining a quadrilateral block) and
`w₁` can in turn replace `w₂` in a different block `B₂`, then exchanging twice
produces a packing of the same cardinality whose covered set is
`(∪S).erase w₂ ∪ {u}`: `w₁` is reabsorbed by the second exchange. -/
theorem exists_two_step_exchange [DecidableRel G.Adj] {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S) {u w₁ w₂ : V} {B₁ B₂ : Finset V}
    (hu : u ∉ S.biUnion id) (hB₁ : B₁ ∈ S) (hw₁ : w₁ ∈ B₁)
    (hBw₁ : G.IsQuadBlock (insert u (B₁.erase w₁)))
    (hB₂ : B₂ ∈ S.erase B₁) (hw₂ : w₂ ∈ B₂)
    (hBw₂ : G.IsQuadBlock (insert w₁ (B₂.erase w₂))) :
    ∃ S'' : Finset (Finset V), G.IsQuadPacking S'' ∧ S''.card = S.card ∧
      S''.biUnion id = (S.biUnion id).erase w₂ ∪ {u} := by
  -- First exchange: `u` replaces `w₁` in `B₁`, giving the packing `S₁`.
  obtain ⟨hP₁, hC₁, hU₁⟩ := hS.exchange_block hu hB₁ hw₁ hBw₁
  -- Book-keeping: `w₁`, `w₂` are covered, `u` is not, and `w₁ ≠ w₂`.
  have hw₁X : w₁ ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB₁ hw₁
  have hB₂S : B₂ ∈ S := (Finset.mem_erase.1 hB₂).2
  have hw₂X : w₂ ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB₂S hw₂
  have hdisj12 : Disjoint B₁ B₂ :=
    hS.2 B₁ hB₁ B₂ hB₂S (Finset.mem_erase.1 hB₂).1.symm
  have hw₁w₂ : w₁ ≠ w₂ := by
    rintro rfl
    exact Finset.disjoint_left.1 hdisj12 hw₁ hw₂
  have hw₁u : w₁ ≠ u := by
    rintro rfl
    exact hu hw₁X
  have hw₂u : w₂ ≠ u := by
    rintro rfl
    exact hu hw₂X
  -- `w₁` is uncovered by `S₁`: it is missing from `(∪S).erase w₁` and `w₁ ≠ u`.
  have hw₁nin : w₁ ∉
      (insert (insert u (B₁.erase w₁)) (S.erase B₁)).biUnion id := by
    rw [hU₁, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    rintro (⟨h, -⟩ | h)
    · exact h rfl
    · exact hw₁u h
  -- `B₂` is still a block of `S₁` since `B₂ ∈ S.erase B₁`.
  have hB₂in : B₂ ∈ insert (insert u (B₁.erase w₁)) (S.erase B₁) :=
    Finset.mem_insert.2 (Or.inr hB₂)
  -- Second exchange: `w₁` replaces `w₂` in `B₂`, giving the packing `S₂`.
  obtain ⟨hP₂, hC₂, hU₂⟩ := hP₁.exchange_block hw₁nin hB₂in hw₂ hBw₂
  refine ⟨_, hP₂, hC₂.trans hC₁, ?_⟩
  rw [hU₂, hU₁]
  -- Set algebra: `((X.erase w₁ ∪ {u}).erase w₂) ∪ {w₁} = X.erase w₂ ∪ {u}`.
  ext x
  by_cases hx₁ : x = w₁
  · subst hx₁
    simp [hw₁w₂, hw₁X]
  · by_cases hx₂ : x = w₂
    · subst hx₂
      simp [hx₁, hw₂u]
    · by_cases hxu : x = u
      · subst hxu
        simp [hx₁, hx₂]
      · simp [hx₁, hx₂, hxu]

/-- **Two-step exchange, leftover form.** Under the hypotheses of
`exists_two_step_exchange`, the leftover of the twice-exchanged packing is
`(univ \ ∪S).erase u ∪ {w₂}`: `u` is absorbed and `w₂` is freed. -/
theorem exists_two_step_exchange_leftover [DecidableRel G.Adj]
    {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S) {u w₁ w₂ : V} {B₁ B₂ : Finset V}
    (hu : u ∉ S.biUnion id) (hB₁ : B₁ ∈ S) (hw₁ : w₁ ∈ B₁)
    (hBw₁ : G.IsQuadBlock (insert u (B₁.erase w₁)))
    (hB₂ : B₂ ∈ S.erase B₁) (hw₂ : w₂ ∈ B₂)
    (hBw₂ : G.IsQuadBlock (insert w₁ (B₂.erase w₂))) :
    ∃ S'' : Finset (Finset V), G.IsQuadPacking S'' ∧ S''.card = S.card ∧
      Finset.univ \ S''.biUnion id =
        (Finset.univ \ S.biUnion id).erase u ∪ {w₂} := by
  obtain ⟨S'', hP, hC, hU⟩ :=
    exists_two_step_exchange hS hu hB₁ hw₁ hBw₁ hB₂ hw₂ hBw₂
  have hB₂S : B₂ ∈ S := (Finset.mem_erase.1 hB₂).2
  have hw₂X : w₂ ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB₂S hw₂
  have hw₂u : w₂ ≠ u := by
    rintro rfl
    exact hu hw₂X
  refine ⟨S'', hP, hC, ?_⟩
  rw [hU]
  -- Set algebra: `univ \ (X.erase w₂ ∪ {u}) = (univ \ X).erase u ∪ {w₂}`.
  ext x
  by_cases hx₂ : x = w₂
  · subst hx₂
    simp [hw₂u]
  · by_cases hxu : x = u
    · subst hxu
      simp [hx₂]
    · simp [hx₂, hxu]

end SimpleGraph
