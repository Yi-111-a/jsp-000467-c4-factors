import JSP467.WChain
import JSP467.WCount

/-!
# JSP-000467 — Wang's finish skeleton for the 9-charge quad

In the counting finish of Wang (Wa10), a quadrilateral block `Q` receives
a charge of `9` from the leftover set `F = {x₀, x₁, x₂, x₃}`; the charge
splits as `e(F, Q) = e(x₀, Q) + e(x₁, Q) + e({x₂,x₃}, Q)` and the pendant
edge `x₀x₁` forces `2 * e(x₀, Q) + e({x₂,x₃}, Q) ≥ 9` (see `WNine`).

This file closes the argument *modulo* Wang's three key claims, stated as
hypotheses to be discharged elsewhere:

* Claim 2.6 — `e(x₀, Q) = 4` forces `e({x₂,x₃}, Q) = 0`;
* Claim 2.7 — `e(x₀, Q) = 3` forces `e({x₂,x₃}, Q) ≤ 2`;
* Claim 2.5 — `e({x₀,x₂,x₃}, Q) ≥ 7` with `e(x₀, Q) ≥ 1` forces either the
  contradictory `e(x₀, Q) = 0`, or `e(x₀, Q) = 1` with
  `e({x₂,x₃}, Q) = 6` (and `N(x₂) ∩ Q = N(x₃) ∩ Q`).

Together with the trivial bounds `e(x₀, Q) ≤ 4` and `e({x₂,x₃}, Q) ≤ 8`
(`crossEdges_singleton_le`, `crossEdges_pair_le`), every case gives
`2 * e(x₀, Q) + e({x₂,x₃}, Q) ≤ 8 < 9`, contradiction.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

/-- A single vertex sends at most `|B| = 4` cross edges into a quad `B`. -/
theorem crossEdges_singleton_le {B : Finset V} {x : V} (hB : B.card = 4) :
    crossEdges G {x} B ≤ 4 := by
  calc crossEdges G {x} B = (B ∩ G.neighborFinset x).card := by
        simp [crossEdges]
    _ ≤ B.card := Finset.card_le_card Finset.inter_subset_left
    _ = 4 := hB

/-- Two distinct vertices send at most `2 * |B| = 8` cross edges into a
quad `B`. -/
theorem crossEdges_pair_le {B : Finset V} {x y : V} (hxy : x ≠ y)
    (hB : B.card = 4) :
    crossEdges G {x, y} B ≤ 8 := by
  have h : crossEdges G {x, y} B
      = (B ∩ G.neighborFinset x).card + (B ∩ G.neighborFinset y).card := by
    unfold crossEdges
    exact Finset.sum_pair hxy
  rw [h]
  have hx : (B ∩ G.neighborFinset x).card ≤ 4 :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq hB
  have hy : (B ∩ G.neighborFinset y).card ≤ 4 :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq hB
  omega

/-- Wang's finish: the charge inequality
`2 * e(x₀, Q) + e({x₂,x₃}, Q) ≥ 9` on a quad `Q` is incompatible with
Claims 2.5, 2.6 and 2.7 of (Wa10).

* `e(x₀, Q) = 4` gives `8 + 0 < 9` by Claim 2.6;
* `e(x₀, Q) = 3` gives `6 + 2 < 9` by Claim 2.7;
* `e(x₀, Q) ≤ 2` gives `e({x₀,x₂,x₃}, Q) ≥ 9 - e(x₀, Q) ≥ 7`, so Claim 2.5
  applies when `e(x₀, Q) ≥ 1`: either `e(x₀, Q) = 0` (contradicting
  `e(x₀, Q) ≥ 1`), or `e(x₀, Q) = 1 ∧ e({x₂,x₃}, Q) = 6`, giving
  `2 + 6 = 8 < 9`.  When `e(x₀, Q) = 0` directly,
  `e({x₂,x₃}, Q) ≥ 9` contradicts `e({x₂,x₃}, Q) ≤ 8`. -/
theorem wang_finish_of_claims
    {T : Finset V} {S : Finset (Finset V)} {x0 x1 x2 x3 : V} {Q : Finset V}
    (hQcard : Q.card = 4)
    (h9 : 9 ≤ 2 * crossEdges G {x0} Q + crossEdges G {x2, x3} Q)
    (hx2x3 : x2 ≠ x3) (hx02 : x0 ≠ x2) (hx03 : x0 ≠ x3)
    (h26 : crossEdges G {x0} Q = 4 → crossEdges G {x2, x3} Q = 0)
    (h27 : crossEdges G {x0} Q = 3 → crossEdges G {x2, x3} Q ≤ 2)
    (h25 : 7 ≤ crossEdges G {x0, x2, x3} Q → crossEdges G {x0} Q ≥ 1 →
      crossEdges G {x0} Q = 0 ∨
        (crossEdges G {x0} Q = 1 ∧ crossEdges G {x2, x3} Q = 6)) :
    False := by
  have he0 : crossEdges G {x0} Q ≤ 4 := crossEdges_singleton_le hQcard
  have he23 : crossEdges G {x2, x3} Q ≤ 8 := crossEdges_pair_le hx2x3 hQcard
  have hmem : x0 ∉ ({x2, x3} : Finset V) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim hx02 hx03
  have hsplit : crossEdges G {x0, x2, x3} Q
      = crossEdges G {x0} Q + crossEdges G {x2, x3} Q := by
    unfold crossEdges
    rw [Finset.sum_insert hmem, Finset.sum_singleton]
  by_cases h4 : crossEdges G {x0} Q = 4
  · have hz := h26 h4
    omega
  · by_cases h3 : crossEdges G {x0} Q = 3
    · have hz := h27 h3
      omega
    · have he02 : crossEdges G {x0} Q ≤ 2 := by omega
      by_cases h0 : crossEdges G {x0} Q = 0
      · omega
      · have hge1 : crossEdges G {x0} Q ≥ 1 := by omega
        have h7 : 7 ≤ crossEdges G {x0, x2, x3} Q := by omega
        rcases h25 h7 hge1 with h | ⟨h1, h6⟩
        · omega
        · omega

end SimpleGraph
