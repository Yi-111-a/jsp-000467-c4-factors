import JSP467.Main
import JSP467.Exchange

/-!
# JSP-000467 — two-quad enlargement inside `U ∪ B`

A strictly stronger enlargement pattern than the single exchange: if the
leftover `U` together with one block `B` of the packing contains **two**
vertex-disjoint quadrilateral blocks `Q₁, Q₂`, then replacing `B` by
`{Q₁, Q₂}` enlarges the packing by one.

This is the pattern that drives Wang's switching argument: once an exchange
`u ↔ w` frees `w`, a quadrilateral inside `U \ {u} ∪ {w}` gives one block, and
the complementary part `{u} ∪ (B \ {w})` may supply the second.  More
generally the two blocks can share `B`'s vertices in any split `(4,0)`,
`(3,1)`, `(2,2)`, `(1,3)`, `(0,4)`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- If `U ∪ B` (the leftover plus one packing block) contains two disjoint
quadrilateral blocks, the packing can be enlarged: replace `B` by both. -/
theorem exists_larger_of_two_blocks {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S) {B Q₁ Q₂ : Finset V} (hB : B ∈ S)
    (hQ₁ : G.IsQuadBlock Q₁) (hQ₂ : G.IsQuadBlock Q₂)
    (hd : Disjoint Q₁ Q₂)
    (hQ₁sub : Q₁ ⊆ Finset.univ \ (S.erase B).biUnion id)
    (hQ₂sub : Q₂ ⊆ Finset.univ \ (S.erase B).biUnion id) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  classical
  have hQ₁ne : Q₁.Nonempty := Finset.card_pos.1 (by rw [hQ₁.1]; exact Nat.succ_pos 3)
  have hQ₂ne : Q₂.Nonempty := Finset.card_pos.1 (by rw [hQ₂.1]; exact Nat.succ_pos 3)
  have hne : Q₁ ≠ Q₂ := by
    intro h
    obtain ⟨x, hx⟩ := hQ₁ne
    exact Finset.disjoint_left.1 hd hx (h ▸ hx)
  -- The new blocks are disjoint from every old block.
  have hdisj₁ : ∀ C ∈ S.erase B, Disjoint Q₁ C := fun C hC =>
    Finset.disjoint_left.2 fun x hxQ hxC =>
      (Finset.mem_sdiff.1 (hQ₁sub hxQ)).2 (Finset.mem_biUnion.2 ⟨C, hC, hxC⟩)
  have hdisj₂ : ∀ C ∈ S.erase B, Disjoint Q₂ C := fun C hC =>
    Finset.disjoint_left.2 fun x hxQ hxC =>
      (Finset.mem_sdiff.1 (hQ₂sub hxQ)).2 (Finset.mem_biUnion.2 ⟨C, hC, hxC⟩)
  have hQ₁nin : Q₁ ∉ S.erase B := fun h => by
    obtain ⟨x, hx⟩ := hQ₁ne
    exact (Finset.mem_sdiff.1 (hQ₁sub hx)).2
      (Finset.mem_biUnion.2 ⟨Q₁, h, hx⟩)
  have hQ₂nin : Q₂ ∉ S.erase B := fun h => by
    obtain ⟨x, hx⟩ := hQ₂ne
    exact (Finset.mem_sdiff.1 (hQ₂sub hx)).2
      (Finset.mem_biUnion.2 ⟨Q₂, h, hx⟩)
  refine ⟨insert Q₁ (insert Q₂ (S.erase B)), ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hQ₁
    · rcases Finset.mem_insert.1 ht with rfl | ht
      · exact hQ₂
      · exact hS.1 t (Finset.mem_erase.1 ht).2
  · intro t₁ h₁ t₂ h₂ hnet
    rcases Finset.mem_insert.1 h₁ with h₁e | h₁
    · rcases Finset.mem_insert.1 h₂ with h₂e | h₂
      · exact absurd (h₁e.trans h₂e.symm) hnet
      · rcases Finset.mem_insert.1 h₂ with h₂e' | h₂mem
        · exact h₁e ▸ h₂e' ▸ hd
        · exact h₁e ▸ hdisj₁ _ h₂mem
    · rcases Finset.mem_insert.1 h₁ with h₁e' | h₁mem
      · rcases Finset.mem_insert.1 h₂ with h₂e | h₂
        · exact h₁e' ▸ h₂e ▸ hd.symm
        · rcases Finset.mem_insert.1 h₂ with h₂e' | h₂mem
          · exact absurd (h₁e'.trans h₂e'.symm) hnet
          · exact h₁e' ▸ hdisj₂ _ h₂mem
      · rcases Finset.mem_insert.1 h₂ with h₂e | h₂
        · exact h₂e ▸ (hdisj₁ _ h₁mem).symm
        · rcases Finset.mem_insert.1 h₂ with h₂e' | h₂mem
          · exact h₂e' ▸ (hdisj₂ _ h₁mem).symm
          · exact hS.2 t₁ (Finset.mem_erase.1 h₁mem).2 t₂
              (Finset.mem_erase.1 h₂mem).2 hnet
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_erase_add_one hB]
    · omega
    · exact hQ₂nin
    · rw [Finset.mem_insert]
      exact fun h => h.elim hne hQ₁nin

end SimpleGraph
