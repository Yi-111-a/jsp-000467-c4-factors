import JSP467.Defs
import Mathlib.Data.Finset.Card

/-!
# JSP-000467 — partition into 4-blocks; the complete-graph case

Milestone lemmas for the Wang (Wa10) formalization: every finset whose
cardinality is a multiple of four splits into 4-element blocks, hence the
complete graph on `4k` vertices admits a spanning quadrilateral factor.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Any finset of cardinal `4 * k` partitions into `k` blocks of four vertices. -/
theorem exists_four_partition {k : ℕ} : ∀ {s : Finset V}, s.card = 4 * k →
    ∃ S : Finset (Finset V),
      (∀ t ∈ S, t ⊆ s ∧ t.card = 4) ∧
      (∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → Disjoint t₁ t₂) ∧
      S.biUnion id = s := by
  induction k with
  | zero =>
    intro s hs
    have hs0 : s = ∅ := Finset.card_eq_zero.1 (by omega)
    subst hs0
    exact ⟨∅, by simp, by simp, by simp⟩
  | succ k ih =>
    intro s hs
    obtain ⟨t, hts, htcard⟩ :=
      Finset.le_card_iff_exists_subset_card.1 (by omega : 4 ≤ s.card)
    have hsdiff : (s \ t).card = 4 * k := by
      rw [Finset.card_sdiff_of_subset hts, hs, htcard]; omega
    obtain ⟨S', hsub, hpair, hcov⟩ := ih hsdiff
    refine ⟨insert t S', ?_, ?_, ?_⟩
    · intro u hu
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact ⟨hts, htcard⟩
      · obtain ⟨hus, huc⟩ := hsub u hu
        exact ⟨hus.trans Finset.sdiff_subset, huc⟩
    · intro t₁ h₁ t₂ h₂ hne
      rcases Finset.mem_insert.1 h₁ with rfl | h₁mem
      · rcases Finset.mem_insert.1 h₂ with rfl | h₂mem
        · exact absurd rfl hne
        · exact Finset.disjoint_sdiff.mono_right (hsub t₂ h₂mem).1
      · rcases Finset.mem_insert.1 h₂ with rfl | h₂mem
        · exact (Finset.disjoint_sdiff.mono_right (hsub t₁ h₁mem).1).symm
        · exact hpair t₁ h₁mem t₂ h₂mem hne
    · rw [Finset.biUnion_insert, hcov, union_comm]
      exact Finset.sdiff_union_of_subset hts

/-- Every 4-element vertex set is a quadrilateral block of the complete graph. -/
theorem isQuadBlock_top {s : Finset V} (hs : s.card = 4) :
    (⊤ : SimpleGraph V).IsQuadBlock s := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ :=
    Finset.card_eq_four.1 hs
  exact IsQuadBlock.of_cycle rfl hab hac had hbc hbd hcd
    ((top_adj _ _).2 hab) ((top_adj _ _).2 hbc) ((top_adj _ _).2 hcd)
    ((top_adj _ _).2 (Ne.symm had))

/-- The complete graph on `4k` vertices has a spanning quadrilateral factor
(the high-degree end of the Erdős–Faudree/Wang phenomenon). -/
theorem completeGraph_hasQuadFactor (h : 4 ∣ Fintype.card V) :
    (⊤ : SimpleGraph V).HasQuadFactor := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨S, hsub, hpair, hcov⟩ :=
    exists_four_partition (by simp [Finset.card_univ, hk] : (univ : Finset V).card = 4 * k)
  exact ⟨S, fun s hs => isQuadBlock_top (hsub s hs).2, hpair, hcov⟩

end SimpleGraph
