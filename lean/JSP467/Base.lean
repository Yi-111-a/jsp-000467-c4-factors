import JSP467.Defs
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# JSP-000467 — base case `k = 1`

Every finite simple graph on four vertices with minimum degree at least two
contains a quadrilateral.  The proof is a direct case analysis on the
adjacency pattern: every vertex has at least two neighbours among the other
three, so no vertex can miss two distinct vertices, and chasing this through
the finitely many cases always produces a four-cycle.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Base case `k = 1` of the Erdős–Faudree/Wang theorem: every finite simple
graph on 4 vertices with minimum degree at least 2 contains a quadrilateral,
i.e. has a spanning quad factor. -/
theorem hasQuadFactor_of_card_eq_four (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 4) (hmin : 2 ≤ G.minDegree) : G.HasQuadFactor := by
  classical
  have huniv : (Finset.univ : Finset V).card = 4 := by
    rw [Finset.card_univ, hcard]
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, _hU⟩ :=
    Finset.card_eq_four.1 huniv
  -- A vertex has at least two neighbours among the other three vertices,
  -- so it cannot be non-adjacent to two distinct vertices.
  have two_nbrs : ∀ {v x y : V}, v ≠ x → v ≠ y → x ≠ y →
      ¬ G.Adj v x → ¬ G.Adj v y → False := by
    intro v x y hvx hvy hxy hax hay
    have hdeg : 2 ≤ (G.neighborFinset v).card :=
      hmin.trans (G.minDegree_le_degree v)
    have hsub : G.neighborFinset v ⊆ ((Finset.univ.erase v).erase x).erase y := by
      intro w hw
      rw [G.mem_neighborFinset] at hw
      have hwv : w ≠ v := (G.ne_of_adj hw).symm
      have hwx : w ≠ x := fun h => hax (h ▸ hw)
      have hwy : w ≠ y := fun h => hay (h ▸ hw)
      rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_erase]
      exact ⟨hwy, hwx, hwv, Finset.mem_univ w⟩
    have hle : (G.neighborFinset v).card ≤ 1 := by
      have h := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hxy.symm,
            Finset.mem_erase.2 ⟨hvy.symm, Finset.mem_univ y⟩⟩),
        Finset.card_erase_of_mem
          (Finset.mem_erase.2 ⟨hvx.symm, Finset.mem_univ x⟩),
        Finset.card_erase_of_mem (Finset.mem_univ v), huniv] at h
      omega
    omega
  -- Hence one missing neighbour forces all the other adjacencies.
  have nbr_of_not : ∀ {v x y : V}, v ≠ x → v ≠ y → x ≠ y →
      ¬ G.Adj v x → G.Adj v y := by
    intro v x y hvx hvy hxy hax
    by_contra hay
    exact two_nbrs hvx hvy hxy hax hay
  -- Packaging: four distinct vertices carrying a cyclic edge pattern give a
  -- quadrilateral block covering all vertices, hence a quad factor.
  have finish : ∀ {x₁ x₂ x₃ x₄ : V},
      x₁ ≠ x₂ → x₁ ≠ x₃ → x₁ ≠ x₄ → x₂ ≠ x₃ → x₂ ≠ x₄ → x₃ ≠ x₄ →
      G.Adj x₁ x₂ → G.Adj x₂ x₃ → G.Adj x₃ x₄ → G.Adj x₄ x₁ →
      G.HasQuadFactor := by
    intro x₁ x₂ x₃ x₄ h12 h13 h14 h23 h24 h34 e1 e2 e3 e4
    have hc4 : ({x₁, x₂, x₃, x₄} : Finset V).card = 4 :=
      Finset.card_eq_four.2 ⟨x₁, x₂, x₃, x₄, h12, h13, h14, h23, h24, h34, rfl⟩
    have hs : (Finset.univ : Finset V) = {x₁, x₂, x₃, x₄} :=
      (Finset.eq_univ_of_card _ (hc4.trans hcard.symm)).symm
    exact HasQuadFactor.of_block_eq_univ rfl
      (IsQuadBlock.of_cycle hs h12 h13 h14 h23 h24 h34 e1 e2 e3 e4)
  by_cases hab' : G.Adj a b
  · by_cases hac' : G.Adj a c
    · by_cases had' : G.Adj a d
      · -- `a` is adjacent to all of `b, c, d`.
        by_cases hbc' : G.Adj b c
        · by_cases hcd' : G.Adj c d
          · -- cycle a - b - c - d - a
            exact finish hab hac had hbc hbd hcd hab' hbc' hcd' had'.symm
          · -- ¬ c ~ d forces d ~ b; cycle a - d - b - c - a
            have hdb : G.Adj d b :=
              nbr_of_not hcd.symm hbd.symm hbc.symm (fun h => hcd' h.symm)
            exact finish had hab hac hbd.symm hcd.symm hbc had' hdb hbc' hac'.symm
        · -- ¬ b ~ c forces b ~ d and c ~ d; cycle a - b - d - c - a
          have hbd' : G.Adj b d := nbr_of_not hbc hbd hcd hbc'
          have hcd' : G.Adj c d :=
            nbr_of_not hbc.symm hcd hbd (fun h => hbc' h.symm)
          exact finish hab had hac hbd hbc hcd.symm hab' hbd' hcd'.symm hac'.symm
      · -- ¬ a ~ d forces d ~ b and d ~ c; cycle a - b - d - c - a
        have hdb : G.Adj d b :=
          nbr_of_not had.symm hbd.symm hab (fun h => had' h.symm)
        have hdc : G.Adj d c :=
          nbr_of_not had.symm hcd.symm hac (fun h => had' h.symm)
        exact finish hab had hac hbd hbc hcd.symm hab' hdb.symm hdc hac'.symm
    · -- ¬ a ~ c forces a ~ d, c ~ b and c ~ d; cycle a - b - c - d - a
      have had' : G.Adj a d := nbr_of_not hac had hcd hac'
      have hcb : G.Adj c b :=
        nbr_of_not hac.symm hbc.symm hab (fun h => hac' h.symm)
      have hcd' : G.Adj c d :=
        nbr_of_not hac.symm hcd had (fun h => hac' h.symm)
      exact finish hab hac had hbc hbd hcd hab' hcb.symm hcd' had'.symm
  · by_cases hac' : G.Adj a c
    · -- ¬ a ~ b forces a ~ d, b ~ c and b ~ d; cycle a - c - b - d - a
      have had' : G.Adj a d := nbr_of_not hab had hbd hab'
      have hbc' : G.Adj b c :=
        nbr_of_not hab.symm hbc hac (fun h => hab' h.symm)
      have hbd' : G.Adj b d :=
        nbr_of_not hab.symm hbd had (fun h => hab' h.symm)
      exact finish hac hab had hbc.symm hcd hbd hac' hbc'.symm hbd' had'.symm
    · -- `a` misses both `b` and `c`, contradicting δ ≥ 2.
      exact (two_nbrs hab hac hbc hab' hac').elim

end SimpleGraph
