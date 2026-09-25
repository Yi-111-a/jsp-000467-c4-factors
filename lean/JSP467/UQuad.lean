import JSP467.Through
import JSP467.Clean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# JSP-000467 — quadrilateral blocks inside subsets with high induced degree

If `U` is a set of `4 * ℓ` vertices (`ℓ ≥ 3`) such that the induced subgraph
`G.induce ↑U` has minimum degree at least `2 * ℓ - 1`, then the pigeonhole
lemma `exists_isQuadBlock_self` applies to the induced subgraph (since
`4 * ℓ < (2 * ℓ - 1) * (2 * ℓ - 2) + 1`), producing a quadrilateral block of
`G` contained in `U`.  The boundary case `ℓ = 2` (eight vertices, minimum
degree four) works as well since `8 < 4 * 3 + 1`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finset `U` of `4ℓ` vertices (`ℓ ≥ 3`) whose induced subgraph has
minimum degree `≥ 2ℓ - 1` contains a quadrilateral block of `G`. -/
theorem exists_quadBlock_of_induce_minDegree (G : SimpleGraph V)
    [DecidableRel G.Adj] {U : Finset V} {ℓ : ℕ} (hℓ : 3 ≤ ℓ)
    (hUcard : U.card = 4 * ℓ) (hUne : U.Nonempty)
    (hmin : 2 * ℓ - 1 ≤ (G.induce (↑U : Set V)).minDegree) :
    ∃ Q : Finset V, G.IsQuadBlock Q ∧ Q ⊆ U := by
  classical
  obtain ⟨u0, hu0⟩ := hUne
  haveI : Nonempty ↥(↑U : Set V) := ⟨⟨u0, Finset.mem_coe.2 hu0⟩⟩
  -- The induced subgraph on `U` has `4 * ℓ` vertices.
  have hGUcard : Fintype.card ↥(↑U : Set V) = 4 * ℓ := by
    have hc : Fintype.card ↥(↑U : Set V) = U.card := by
      rw [← Set.toFinset_card, Finset.toFinset_coe]
    rw [hc, hUcard]
  -- `4 * ℓ < (2ℓ - 1) * (2ℓ - 2) + 1` for `ℓ ≥ 3`.
  have hbig : Fintype.card ↥(↑U : Set V)
      < (2 * ℓ - 1) * (2 * ℓ - 1 - 1) + 1 := by
    rw [hGUcard]
    have hA : (2 * ℓ - 1) * 4 ≤ (2 * ℓ - 1) * (2 * ℓ - 1 - 1) :=
      Nat.mul_le_mul le_rfl (by omega)
    have hB : 4 * ℓ ≤ (2 * ℓ - 1) * 4 := by
      rw [Nat.mul_comm 4 ℓ]
      exact Nat.mul_le_mul (by omega) le_rfl
    omega
  -- Apply the pigeonhole lemma to a vertex of the induced subgraph and lift.
  obtain ⟨v0⟩ : Nonempty ↥(↑U : Set V) := ⟨⟨u0, Finset.mem_coe.2 hu0⟩⟩
  obtain ⟨t, htb, -⟩ :=
    (G.induce (↑U : Set V)).exists_isQuadBlock_self v0 hmin hbig
  obtain ⟨hQblk, hQsub⟩ := IsQuadBlock.of_induce htb
  exact ⟨t.image Subtype.val, hQblk,
    fun x hx => Finset.mem_coe.1 (hQsub x hx)⟩

/-- The boundary case `ℓ = 2`: a finset `U` of eight vertices whose induced
subgraph has minimum degree `≥ 4` contains a quadrilateral block of `G`. -/
theorem exists_quadBlock_of_induce_minDegree_l2 (G : SimpleGraph V)
    [DecidableRel G.Adj] {U : Finset V} (hUcard : U.card = 8)
    (hUne : U.Nonempty)
    (hmin : 4 ≤ (G.induce (↑U : Set V)).minDegree) :
    ∃ Q : Finset V, G.IsQuadBlock Q ∧ Q ⊆ U := by
  classical
  obtain ⟨u0, hu0⟩ := hUne
  haveI : Nonempty ↥(↑U : Set V) := ⟨⟨u0, Finset.mem_coe.2 hu0⟩⟩
  have hGUcard : Fintype.card ↥(↑U : Set V) = 8 := by
    have hc : Fintype.card ↥(↑U : Set V) = U.card := by
      rw [← Set.toFinset_card, Finset.toFinset_coe]
    rw [hc, hUcard]
  -- `8 < 4 * 3 + 1 = 13`.
  have hbig : Fintype.card ↥(↑U : Set V) < 4 * (4 - 1) + 1 := by
    rw [hGUcard]
    omega
  obtain ⟨v0⟩ : Nonempty ↥(↑U : Set V) := ⟨⟨u0, Finset.mem_coe.2 hu0⟩⟩
  -- placeholder
  obtain ⟨t, htb, -⟩ :=
    (G.induce (↑U : Set V)).exists_isQuadBlock_self v0 hmin hbig
  obtain ⟨hQblk, hQsub⟩ := IsQuadBlock.of_induce htb
  exact ⟨t.image Subtype.val, hQblk,
    fun x hx => Finset.mem_coe.1 (hQsub x hx)⟩

end SimpleGraph
