import JSP467.Main
import JSP467.Pairing

/-!
# JSP-000467 — packing-level exchange machinery

Enlargement and exchange steps for quadrilateral packings (`IsQuadPacking`),
used by the proof of the Erdős–Faudree conjecture (Wang, Wa10):

* `IsQuadPacking.enlarge` — a quadrilateral block disjoint from the covered
  vertices extends a packing by one.
* `exists_larger_of_leftover_block` — a quadrilateral block inside the
  leftover vertices yields a strictly larger packing.
* `IsQuadPacking.exchange_block` — swapping a vertex `w` of a packing block
  `B` for an uncovered vertex `u` (keeping block-ness) yields a packing of
  the same cardinality covering `(∪S).erase w ∪ {u}`.
* `exists_exchange_packing` — the `≥ 3` neighbours condition that produces
  such a `w` (via `IsQuadBlock.exchange`).
* `exists_larger_of_exchange_leftover_block` — after an exchange, a
  quadrilateral block inside the new leftover set yields a larger packing.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
/-- A quadrilateral block disjoint from every covered vertex extends a
packing by one element. -/
theorem IsQuadPacking.enlarge {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S) {Q : Finset V} (hQ : G.IsQuadBlock Q)
    (hd : Disjoint Q (S.biUnion id)) :
    G.IsQuadPacking (insert Q S) ∧ (insert Q S).card = S.card + 1 := by
  have hQne : Q.Nonempty := Finset.card_pos.1 (by rw [hQ.1]; exact Nat.succ_pos 3)
  have hQnS : Q ∉ S := by
    intro hQS
    obtain ⟨a, ha⟩ := hQne
    exact Finset.disjoint_left.1 hd ha
      (Finset.subset_biUnion_of_mem id hQS ha)
  have hdisj : ∀ t ∈ S, Disjoint Q t :=
    fun t ht => (Finset.disjoint_biUnion_right Q S id).1 hd t ht
  refine ⟨⟨?_, ?_⟩, Finset.card_insert_of_notMem hQnS⟩
  · intro t ht
    rcases Finset.mem_insert.1 ht with ht | ht
    · exact ht ▸ hQ
    · exact hS.1 t ht
  · intro t₁ h₁ t₂ h₂ hne
    rcases Finset.mem_insert.1 h₁ with ht₁ | h₁
    · rcases Finset.mem_insert.1 h₂ with ht₂ | h₂
      · exact absurd (ht₁.trans ht₂.symm) hne
      · exact ht₁ ▸ hdisj t₂ h₂
    · rcases Finset.mem_insert.1 h₂ with ht₂ | h₂
      · exact ht₂ ▸ (hdisj t₁ h₁).symm
      · exact hS.2 t₁ h₁ t₂ h₂ hne

/-- A quadrilateral block contained in the leftover vertices yields a
strictly larger packing. -/
theorem exists_larger_of_leftover_block {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S) {Q : Finset V} (hQ : G.IsQuadBlock Q)
    (hQU : Q ⊆ Finset.univ \ S.biUnion id) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  have hd : Disjoint Q (S.biUnion id) := Finset.disjoint_left.2 fun a ha haU =>
    (Finset.mem_sdiff.1 (hQU ha)).2 haU
  obtain ⟨hT, hcard⟩ := hS.enlarge hQ hd
  exact ⟨insert Q S, hT, by omega⟩

omit [Fintype V] in
/-- Swapping a covered vertex `w` of a packing block `B` for an uncovered
vertex `u` — assuming the swapped set is still a quadrilateral block —
produces a packing of the same cardinality whose covered set is
`(∪S).erase w ∪ {u}`. -/
theorem IsQuadPacking.exchange_block {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S) {u w : V} {B : Finset V}
    (hu : u ∉ S.biUnion id) (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert u (B.erase w))) :
    G.IsQuadPacking (insert (insert u (B.erase w)) (S.erase B)) ∧
      (insert (insert u (B.erase w)) (S.erase B)).card = S.card ∧
      (insert (insert u (B.erase w)) (S.erase B)).biUnion id =
        (S.biUnion id).erase w ∪ {u} := by
  have hBS : B ⊆ S.biUnion id := Finset.subset_biUnion_of_mem id hB
  -- Every other block of `S` is disjoint from the new block: it is disjoint
  -- from `B` (packing) and does not contain `u` (uncovered).
  have hdisj : ∀ C ∈ S.erase B, Disjoint (insert u (B.erase w)) C := by
    intro C hC
    obtain ⟨hCB, hCS⟩ := Finset.mem_erase.1 hC
    have hBC : Disjoint B C := hS.2 B hB C hCS hCB.symm
    have huC : u ∉ C := fun h => hu (Finset.subset_biUnion_of_mem id hCS h)
    rw [Finset.disjoint_insert_left]
    exact ⟨huC, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hBC⟩
  -- The new block is genuinely new: it contains `u`, which no old block does.
  have hB'nin : insert u (B.erase w) ∉ S.erase B := by
    intro h
    exact hu (Finset.subset_biUnion_of_mem id (Finset.mem_erase.1 h).2
      (Finset.mem_insert_self u _))
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro C hC
    rcases Finset.mem_insert.1 hC with rfl | hC
    · exact hBw
    · exact hS.1 C (Finset.mem_erase.1 hC).2
  · intro C₁ h₁ C₂ h₂ hne
    rcases Finset.mem_insert.1 h₁ with rfl | h₁
    · rcases Finset.mem_insert.1 h₂ with rfl | h₂
      · exact absurd rfl hne
      · exact hdisj C₂ h₂
    · rcases Finset.mem_insert.1 h₂ with rfl | h₂
      · exact (hdisj C₁ h₁).symm
      · exact hS.2 C₁ (Finset.mem_erase.1 h₁).2 C₂
          (Finset.mem_erase.1 h₂).2 hne
  · rw [Finset.card_insert_of_notMem hB'nin, Finset.card_erase_add_one hB]
  · -- The covered set: `∪S` splits as `B ⊔ ∪(S.erase B)` (disjoint union).
    have hsplit : S.biUnion id = B ∪ (S.erase B).biUnion id := by
      conv_lhs => rw [← Finset.insert_erase hB]
      rw [Finset.biUnion_insert]
      rfl
    have hdisjB : Disjoint B ((S.erase B).biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro C hC
      obtain ⟨hCB, hCS⟩ := Finset.mem_erase.1 hC
      exact hS.2 B hB C hCS hCB.symm
    have herase : (S.erase B).biUnion id = S.biUnion id \ B := by
      rw [hsplit, Finset.union_sdiff_cancel_left hdisjB]
    -- `B.erase w ∪ (∪S \ B) = (∪S).erase w` since `{w} ⊆ B ⊆ ∪S`.
    have hmerge : B.erase w ∪ (S.biUnion id \ B)
        = (S.biUnion id).erase w := by
      rw [← Finset.sdiff_singleton_eq_erase, ← Finset.sdiff_singleton_eq_erase,
        Finset.union_comm,
        Finset.sdiff_union_sdiff_cancel hBS (Finset.singleton_subset_iff.2 hw)]
    rw [Finset.biUnion_insert, herase]
    simp only [id_eq]
    rw [Finset.insert_eq, Finset.union_assoc, hmerge]
    exact Finset.union_comm _ _

/-- Exchange step: if an uncovered vertex `u` has at least three neighbours
inside a packing block `B`, then some `w ∈ B` can be swapped for `u`,
producing a new packing of the same cardinality covering
`(∪S).erase w ∪ {u}`. -/
theorem exists_exchange_packing [DecidableRel G.Adj] {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S) {u : V} (hu : u ∉ S.biUnion id) {B : Finset V}
    (hB : B ∈ S) (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    ∃ w ∈ B, ∃ S' : Finset (Finset V), G.IsQuadPacking S' ∧
      S'.card = S.card ∧ S'.biUnion id = (S.biUnion id).erase w ∪ {u} := by
  have huB : u ∉ B := fun h => hu (Finset.subset_biUnion_of_mem id hB h)
  obtain ⟨w, hwB, hBw⟩ := IsQuadBlock.exchange (hS.1 B hB) huB h3
  obtain ⟨hp, hc, hU⟩ := hS.exchange_block hu hB hwB hBw
  exact ⟨w, hwB, _, hp, hc, hU⟩

/-- Enlargement test after an exchange: if `w ∈ B` was swapped for the
uncovered `u` (the swapped set still being a quadrilateral block) and a
quadrilateral block `Q` sits inside the new leftover set
`(univ \ ∪S).erase u ∪ {w}`, then a strictly larger packing exists. -/
theorem exists_larger_of_exchange_leftover_block [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) {u w : V} {B : Finset V}
    (hu : u ∉ S.biUnion id) (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert u (B.erase w)))
    {Q : Finset V} (hQ : G.IsQuadBlock Q)
    (hsub : Q ⊆ (Finset.univ \ S.biUnion id).erase u ∪ {w}) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  obtain ⟨hS', hcard', hU'⟩ := hS.exchange_block hu hB hw hBw
  have hwU : w ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB hw
  have hne : w ≠ u := fun h => hu (h ▸ hwU)
  -- `univ \ ∪S' = (univ \ ∪S).erase u ∪ {w}`, so `Q` fits the new leftover.
  have hsub' : Q ⊆ Finset.univ \ (insert (insert u (B.erase w))
      (S.erase B)).biUnion id := by
    intro x hx
    have hx' := hsub hx
    rw [hU']
    simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_sdiff, Finset.mem_univ, true_and] at hx' ⊢
    rcases hx' with ⟨hxu, hxU⟩ | rfl
    · rintro (⟨-, hxU'⟩ | h)
      · exact hxU hxU'
      · exact hxu h
    · rintro (⟨hww, -⟩ | h)
      · exact (hww rfl).elim
      · exact absurd h hne
  obtain ⟨T, hT, hcard⟩ := exists_larger_of_leftover_block hS' hQ hsub'
  exact ⟨T, hT, by omega⟩

end SimpleGraph
