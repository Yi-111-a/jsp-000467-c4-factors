import JSP467.TwoQuads

/-!
# JSP-000467 — three-quad enlargement inside `U ∪ B₁ ∪ B₂`

The two-block analogue of `exists_larger_of_two_blocks`: if the leftover `U`
together with **two** distinct blocks `B₁, B₂` of the packing contains **three**
pairwise-disjoint quadrilateral blocks `Q₁, Q₂, Q₃`, then replacing `B₁` and
`B₂` by `{Q₁, Q₂, Q₃}` enlarges the packing by one.

This is the finishing pattern for the two-block cascade in Wang's switching
argument: once the switching chain spreads into a second packing block, three
quadrilaterals in the two-block region `U ∪ B₁ ∪ B₂` finish the enlargement.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- If `U ∪ B₁ ∪ B₂` (the leftover plus two distinct packing blocks) contains
three pairwise-disjoint quadrilateral blocks, the packing can be enlarged:
replace `B₁, B₂` by all three. -/
theorem exists_larger_of_three_blocks {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S) {B₁ B₂ Q₁ Q₂ Q₃ : Finset V}
    (hB₁ : B₁ ∈ S) (hB₂ : B₂ ∈ S) (hB : B₁ ≠ B₂)
    (hQ₁ : G.IsQuadBlock Q₁) (hQ₂ : G.IsQuadBlock Q₂) (hQ₃ : G.IsQuadBlock Q₃)
    (hd₁₂ : Disjoint Q₁ Q₂) (hd₁₃ : Disjoint Q₁ Q₃) (hd₂₃ : Disjoint Q₂ Q₃)
    (hQ₁sub : Q₁ ⊆ Finset.univ \ ((S.erase B₁).erase B₂).biUnion id)
    (hQ₂sub : Q₂ ⊆ Finset.univ \ ((S.erase B₁).erase B₂).biUnion id)
    (hQ₃sub : Q₃ ⊆ Finset.univ \ ((S.erase B₁).erase B₂).biUnion id) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  classical
  have hQ₁ne : Q₁.Nonempty := Finset.card_pos.1 (by rw [hQ₁.1]; exact Nat.succ_pos 3)
  have hQ₂ne : Q₂.Nonempty := Finset.card_pos.1 (by rw [hQ₂.1]; exact Nat.succ_pos 3)
  have hQ₃ne : Q₃.Nonempty := Finset.card_pos.1 (by rw [hQ₃.1]; exact Nat.succ_pos 3)
  have hne₁₂ : Q₁ ≠ Q₂ := by
    intro h
    obtain ⟨x, hx⟩ := hQ₁ne
    exact Finset.disjoint_left.1 hd₁₂ hx (h ▸ hx)
  have hne₁₃ : Q₁ ≠ Q₃ := by
    intro h
    obtain ⟨x, hx⟩ := hQ₁ne
    exact Finset.disjoint_left.1 hd₁₃ hx (h ▸ hx)
  have hne₂₃ : Q₂ ≠ Q₃ := by
    intro h
    obtain ⟨x, hx⟩ := hQ₂ne
    exact Finset.disjoint_left.1 hd₂₃ hx (h ▸ hx)
  -- The new blocks are disjoint from every old block.
  have hdisj₁ : ∀ C ∈ (S.erase B₁).erase B₂, Disjoint Q₁ C := fun C hC =>
    Finset.disjoint_left.2 fun x hxQ hxC =>
      (Finset.mem_sdiff.1 (hQ₁sub hxQ)).2 (Finset.mem_biUnion.2 ⟨C, hC, hxC⟩)
  have hdisj₂ : ∀ C ∈ (S.erase B₁).erase B₂, Disjoint Q₂ C := fun C hC =>
    Finset.disjoint_left.2 fun x hxQ hxC =>
      (Finset.mem_sdiff.1 (hQ₂sub hxQ)).2 (Finset.mem_biUnion.2 ⟨C, hC, hxC⟩)
  have hdisj₃ : ∀ C ∈ (S.erase B₁).erase B₂, Disjoint Q₃ C := fun C hC =>
    Finset.disjoint_left.2 fun x hxQ hxC =>
      (Finset.mem_sdiff.1 (hQ₃sub hxQ)).2 (Finset.mem_biUnion.2 ⟨C, hC, hxC⟩)
  have hQ₁nin : Q₁ ∉ (S.erase B₁).erase B₂ := fun h => by
    obtain ⟨x, hx⟩ := hQ₁ne
    exact (Finset.mem_sdiff.1 (hQ₁sub hx)).2
      (Finset.mem_biUnion.2 ⟨Q₁, h, hx⟩)
  have hQ₂nin : Q₂ ∉ (S.erase B₁).erase B₂ := fun h => by
    obtain ⟨x, hx⟩ := hQ₂ne
    exact (Finset.mem_sdiff.1 (hQ₂sub hx)).2
      (Finset.mem_biUnion.2 ⟨Q₂, h, hx⟩)
  have hQ₃nin : Q₃ ∉ (S.erase B₁).erase B₂ := fun h => by
    obtain ⟨x, hx⟩ := hQ₃ne
    exact (Finset.mem_sdiff.1 (hQ₃sub hx)).2
      (Finset.mem_biUnion.2 ⟨Q₃, h, hx⟩)
  have hQ₂nin' : Q₂ ∉ insert Q₃ ((S.erase B₁).erase B₂) := by
    rw [Finset.mem_insert]
    exact fun h => h.elim hne₂₃ hQ₂nin
  have hQ₁nin' : Q₁ ∉ insert Q₂ (insert Q₃ ((S.erase B₁).erase B₂)) := by
    rw [Finset.mem_insert, Finset.mem_insert]
    exact fun h => h.elim hne₁₂ fun h' => h'.elim hne₁₃ hQ₁nin
  have hB₂' : B₂ ∈ S.erase B₁ := Finset.mem_erase.2 ⟨hB.symm, hB₂⟩
  refine ⟨insert Q₁ (insert Q₂ (insert Q₃ ((S.erase B₁).erase B₂))), ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hQ₁
    · rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hQ₂
      · rcases Finset.mem_insert.1 ht with rfl | ht
        · exact hQ₃
        · exact hS.1 t (Finset.mem_erase.1 (Finset.mem_erase.1 ht).2).2
  · intro t₁ h₁ t₂ h₂ hnet
    rcases Finset.mem_insert.1 h₁ with h₁e | h₁
    · rcases Finset.mem_insert.1 h₂ with h₂e | h₂
      · exact absurd (h₁e.trans h₂e.symm) hnet
      · rcases Finset.mem_insert.1 h₂ with h₂e' | h₂
        · exact h₁e ▸ h₂e' ▸ hd₁₂
        · rcases Finset.mem_insert.1 h₂ with h₂e'' | h₂mem
          · exact h₁e ▸ h₂e'' ▸ hd₁₃
          · exact h₁e ▸ hdisj₁ _ h₂mem
    · rcases Finset.mem_insert.1 h₁ with h₁e' | h₁
      · rcases Finset.mem_insert.1 h₂ with h₂e | h₂
        · exact h₁e' ▸ h₂e ▸ hd₁₂.symm
        · rcases Finset.mem_insert.1 h₂ with h₂e' | h₂
          · exact absurd (h₁e'.trans h₂e'.symm) hnet
          · rcases Finset.mem_insert.1 h₂ with h₂e'' | h₂mem
            · exact h₁e' ▸ h₂e'' ▸ hd₂₃
            · exact h₁e' ▸ hdisj₂ _ h₂mem
      · rcases Finset.mem_insert.1 h₁ with h₁e'' | h₁mem
        · rcases Finset.mem_insert.1 h₂ with h₂e | h₂
          · exact h₁e'' ▸ h₂e ▸ hd₁₃.symm
          · rcases Finset.mem_insert.1 h₂ with h₂e' | h₂
            · exact h₁e'' ▸ h₂e' ▸ hd₂₃.symm
            · rcases Finset.mem_insert.1 h₂ with h₂e'' | h₂mem
              · exact absurd (h₁e''.trans h₂e''.symm) hnet
              · exact h₁e'' ▸ hdisj₃ _ h₂mem
        · rcases Finset.mem_insert.1 h₂ with h₂e | h₂
          · exact h₂e ▸ (hdisj₁ _ h₁mem).symm
          · rcases Finset.mem_insert.1 h₂ with h₂e' | h₂
            · exact h₂e' ▸ (hdisj₂ _ h₁mem).symm
            · rcases Finset.mem_insert.1 h₂ with h₂e'' | h₂mem
              · exact h₂e'' ▸ (hdisj₃ _ h₁mem).symm
              · exact hS.2 t₁ (Finset.mem_erase.1 (Finset.mem_erase.1 h₁mem).2).2
                  t₂ (Finset.mem_erase.1 (Finset.mem_erase.1 h₂mem).2).2 hnet
  · rw [Finset.card_insert_of_notMem hQ₁nin',
        Finset.card_insert_of_notMem hQ₂nin',
        Finset.card_insert_of_notMem hQ₃nin,
        Finset.card_erase_add_one hB₂',
        Finset.card_erase_add_one hB₁]

/-- Corollary: three pairwise-disjoint quadrilateral blocks inside the
two-block region `U ∪ B₁ ∪ B₂` (the leftover plus the two blocks `B₁, B₂`)
already lie outside every other packing block, hence enlarge the packing. -/
theorem exists_larger_of_two_regions {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S) {B₁ B₂ Q₁ Q₂ Q₃ : Finset V}
    (hB₁ : B₁ ∈ S) (hB₂ : B₂ ∈ S) (hB : B₁ ≠ B₂)
    (hQ₁ : G.IsQuadBlock Q₁) (hQ₂ : G.IsQuadBlock Q₂) (hQ₃ : G.IsQuadBlock Q₃)
    (hd₁₂ : Disjoint Q₁ Q₂) (hd₁₃ : Disjoint Q₁ Q₃) (hd₂₃ : Disjoint Q₂ Q₃)
    (hQ₁sub : Q₁ ⊆ (Finset.univ \ S.biUnion id) ∪ B₁ ∪ B₂)
    (hQ₂sub : Q₂ ⊆ (Finset.univ \ S.biUnion id) ∪ B₁ ∪ B₂)
    (hQ₃sub : Q₃ ⊆ (Finset.univ \ S.biUnion id) ∪ B₁ ∪ B₂) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  classical
  -- Any vertex of `Qᵢ` inside another packing block `C` contradicts the
  -- region hypothesis: `x` would avoid `U`, `B₁`, and `B₂` alike.
  have hsub : ∀ Q : Finset V, Q ⊆ (Finset.univ \ S.biUnion id) ∪ B₁ ∪ B₂ →
      Q ⊆ Finset.univ \ ((S.erase B₁).erase B₂).biUnion id := by
    intro Q hQ x hx
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ x, ?_⟩
    intro hxB
    obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.1 hxB
    obtain ⟨hCB₂, hCer⟩ := Finset.mem_erase.1 hC
    obtain ⟨hCB₁, hCS⟩ := Finset.mem_erase.1 hCer
    have hmem := hQ hx
    rw [Finset.mem_union, Finset.mem_union] at hmem
    rcases hmem with hleft | hxB₁ | hxB₂
    · exact (Finset.mem_sdiff.1 hleft).2 (Finset.mem_biUnion.2 ⟨C, hCS, hxC⟩)
    · have hd : Disjoint B₁ C := hS.2 B₁ hB₁ C hCS fun h => hCB₁ h.symm
      exact Finset.disjoint_left.1 hd hxB₁ hxC
    · have hd : Disjoint B₂ C := hS.2 B₂ hB₂ C hCS fun h => hCB₂ h.symm
      exact Finset.disjoint_left.1 hd hxB₂ hxC
  exact exists_larger_of_three_blocks hS hB₁ hB₂ hB hQ₁ hQ₂ hQ₃ hd₁₂ hd₁₃ hd₂₃
    (hsub Q₁ hQ₁sub) (hsub Q₂ hQ₂sub) (hsub Q₃ hQ₃sub)

end SimpleGraph
