import JSP467.LexMax

/-!
# JSP-000467 — the three-coordinate lexicographic maximizer

Wang's feasible chain is chosen extremal in **two** block invariants before the
residual leftover structure: first `Σ τ(Qᵢ)` (our `blockSum`), then the number
of `τ = 2` blocks — quadrilaterals spanning `K₄`.  The earlier
`exists_lexmax_packing` (in `JSP467.LexMax`) uses only `(blockSum, leftover
edgeSum)`; this file upgrades the objective to the faithful three-coordinate
lexicographic order

`blockSum`  →  `k4Count` (# blocks spanning `K₄`)  →  leftover `edgeSum`,

encoded as the single `ℕ` objective `blockSum * C² + k4Count * C + edgeSum`
with `C = univ.card² + 1` strictly larger than any `edgeSum`, hence also
strictly larger than `k4Count + edgeSum` corrections.

* `k4Count` — number of packing blocks with `edgeSum = 12` (i.e. `K₄`).
* `k4Count_le_card`, `card_mul_four_le_univ` — the bounds needed for the
  packing argument.
* `exists_lexmax3_packing` — the three-coordinate lexicographic maximizer.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The number of blocks of a packing that span `K₄` (twelve ordered adjacent
pairs).  This is the packing analogue of Wang's `|{Qᵢ : τ(Qᵢ) = 2}|`. -/
def k4Count (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) :
    ℕ :=
  (S.filter fun B => edgeSum G B = 12).card

variable [DecidableRel G.Adj]

theorem k4Count_le_card (S : Finset (Finset V)) : k4Count G S ≤ S.card :=
  Finset.card_filter_le _ _

/-- A quadrilateral packing's blocks cover at most all vertices, so its
cardinality is at most `Fintype.card V`. -/
theorem card_mul_four_le_univ {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S) : 4 * S.card ≤ Fintype.card V := by
  have hdisj : (S : Set (Finset V)).PairwiseDisjoint id :=
    fun B hB C hC hne => hS.2 B hB C hC hne
  have hScard : (S.biUnion id).card = 4 * S.card := by
    calc (S.biUnion id).card
        = ∑ B ∈ S, (id B).card := Finset.card_biUnion hdisj
      _ = ∑ _B ∈ S, 4 := Finset.sum_congr rfl fun B hB => (hS.1 B hB).1
      _ = 4 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [← hScard]
  exact Finset.card_le_univ _

theorem k4Count_lt_bound {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    {C : ℕ} (hC : Fintype.card V * Fintype.card V + 1 = C) :
    k4Count G S < C := by
  have h1 := k4Count_le_card (G := G) S
  have h2 := card_mul_four_le_univ (G := G) hS
  omega

/-- **Three-coordinate lexicographic maximizer** — Wang's extremal choice:
maximize `blockSum`, then the number of `K₄` blocks, then the leftover
`edgeSum`. -/
theorem exists_lexmax3_packing (m : ℕ)
    (hne : ∃ S : Finset (Finset V), G.IsQuadPacking S ∧ S.card = m) :
    ∃ S : Finset (Finset V), G.IsQuadPacking S ∧ S.card = m ∧
      ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = m →
        blockSum G T < blockSum G S ∨
          (blockSum G T = blockSum G S ∧ k4Count G T < k4Count G S) ∨
          (blockSum G T = blockSum G S ∧ k4Count G T = k4Count G S ∧
            edgeSum G (Finset.univ \ T.biUnion id) ≤
              edgeSum G (Finset.univ \ S.biUnion id)) := by
  classical
  set C : ℕ := (Finset.univ : Finset V).card * (Finset.univ : Finset V).card + 1
    with hC
  set P : Finset (Finset (Finset V)) :=
    univ.filter fun S => G.IsQuadPacking S ∧ S.card = m with hPdef
  have hmem : ∀ S : Finset (Finset V),
      S ∈ P ↔ G.IsQuadPacking S ∧ S.card = m := by
    intro S
    simp [hPdef]
  obtain ⟨S₀, hS₀⟩ := hne
  have hne' : P.Nonempty := ⟨S₀, (hmem S₀).2 hS₀⟩
  obtain ⟨S, hSP, hSmax⟩ := Finset.exists_max_image P
    (fun S => blockSum G S * (C * C) + k4Count G S * C +
      edgeSum G (Finset.univ \ S.biUnion id)) hne'
  refine ⟨S, ((hmem S).1 hSP).1, ((hmem S).1 hSP).2, ?_⟩
  intro T hT hTm
  have hle := hSmax T ((hmem T).2 ⟨hT, hTm⟩)
  have hSe : edgeSum G (Finset.univ \ S.biUnion id) < C := by
    have h := edgeSum_le_card_sq (G := G) (Finset.univ \ S.biUnion id)
    omega
  have hTe : edgeSum G (Finset.univ \ T.biUnion id) < C := by
    have h := edgeSum_le_card_sq (G := G) (Finset.univ \ T.biUnion id)
    omega
  have hSk : k4Count G S < C := k4Count_lt_bound ((hmem S).1 hSP).1 rfl
  have hTk : k4Count G T < C := k4Count_lt_bound hT rfl
  by_cases hb : blockSum G T < blockSum G S
  · exact Or.inl hb
  · push Not at hb
    -- `blockSum S ≤ blockSum T`; strict increase contradicts maximality.
    by_cases hbt : blockSum G S < blockSum G T
    · have hmul : blockSum G S * (C * C) + C * C
          ≤ blockSum G T * (C * C) := by
        have h : blockSum G S + 1 ≤ blockSum G T := hbt
        have h' := Nat.mul_le_mul h (le_refl (C * C))
        rwa [add_mul, one_mul] at h'
      have hC2 : k4Count G S * C + edgeSum G (Finset.univ \ S.biUnion id)
          < C * C := by
        have h1 : k4Count G S * C ≤ (C - 1) * C := by
          have : k4Count G S + 1 ≤ C := hSk
          have h' := Nat.mul_le_mul this (le_refl C)
          rwa [add_mul, one_mul] at h'
        omega
      omega
    · push Not at hbt
      have hbeq : blockSum G T = blockSum G S := le_antisymm hbt hb
      -- `blockSum` equal: compare `k4Count`.
      by_cases hk : k4Count G T < k4Count G S
      · exact Or.inr (Or.inl ⟨hbeq, hk⟩)
      · push Not at hk
        by_cases hkt : k4Count G S < k4Count G T
        · have hmul : k4Count G S * C + C ≤ k4Count G T * C := by
            have h : k4Count G S + 1 ≤ k4Count G T := hkt
            have h' := Nat.mul_le_mul h (le_refl C)
            rwa [add_mul, one_mul] at h'
          rw [hbeq] at hle
          omega
        · push Not at hkt
          have hkeq : k4Count G T = k4Count G S := le_antisymm hkt hk
          refine Or.inr (Or.inr ⟨hbeq, hkeq, ?_⟩)
          rw [hbeq, hkeq] at hle
          omega

end SimpleGraph
