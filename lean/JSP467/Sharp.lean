import JSP467.CommonNbr

/-!
# JSP-000467 — the degree threshold `2k` is optimal (sharpness)

The headline theorem `JSP467.Top.spanning_c4_factors_min_degree` states that a
graph on `4k` vertices with minimum degree at least `2k` contains `k`
vertex-disjoint quadrilaterals covering all vertices.  This file turns the
sharpness discussion of the catalog statement into theorems:

* `adj_bip` — in `K_{α, β}` every adjacency joins the two sides.
* `IsQuadBlock.card_A`, `IsQuadBlock.card_B` — every quadrilateral block of
  `K_{α, β}` uses exactly two vertices of each side (a `C₄` alternates).
* `card_A_of_quadPacking` — a quadrilateral packing of `K_{α, β}` of
  cardinality `S.card` covers exactly `2 · S.card` vertices of the `α`-side.
* `card_le_card_A`, `card_le_k_sub_one` — hence at most `⌊|α| / 2⌋`
  vertex-disjoint quadrilaterals in `K_{α, β}`.
* `no_quadFactor_knm` — `K_{2k-1, 2k+1}` (order `4k`, minimum degree
  `2k - 1`) has **no** spanning quadrilateral factor.  So the minimum-degree
  hypothesis `δ(G) ≥ 2k` of Wa10 cannot be lowered to `δ(G) ≥ 2k - 1`.
-/

open Finset

namespace SimpleGraph

/-- The `α`-side of the complete bipartite graph on `α ⊕ β`. -/
def bipA (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    Finset (α ⊕ β) := Finset.univ.image (Sum.inl : α → α ⊕ β)

/-- The `β`-side of the complete bipartite graph on `α ⊕ β`. -/
def bipB (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
    Finset (α ⊕ β) := Finset.univ.image (Sum.inr : β → α ⊕ β)

theorem bipA_def {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] : bipA α β = Finset.univ.image (Sum.inl : α → α ⊕ β) := rfl

theorem bipB_def {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] : bipB α β = Finset.univ.image (Sum.inr : β → α ⊕ β) := rfl

/-- Membership in a two-element finset. -/
theorem mem_pair {γ : Type*} [DecidableEq γ] (z p q : γ) (hz : z ∈ ({p, q} : Finset γ)) :
    z = p ∨ z = q := by
  rcases Finset.mem_insert.mp hz with hzp | hz'
  · exact Or.inl hzp
  · exact Or.inr (Finset.mem_singleton.mp hz')

/-- Membership in a three-element finset. -/
theorem mem_triple {γ : Type*} [DecidableEq γ] (z p q r : γ)
    (hz : z ∈ ({p, q, r} : Finset γ)) : z = p ∨ z = q ∨ z = r := by
  rcases Finset.mem_insert.mp hz with h | h
  · exact Or.inl h
  · rcases Finset.mem_insert.mp h with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Finset.mem_singleton.mp h'))

/-- Membership in a four-element finset. -/
theorem mem_four {γ : Type*} [DecidableEq γ] (z p q r t : γ)
    (hz : z ∈ ({p, q, r, t} : Finset γ)) : z = p ∨ z = q ∨ z = r ∨ z = t := by
  rcases Finset.mem_insert.mp hz with h | h
  · exact Or.inl h
  · rcases mem_triple z q r t h with h' | h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))

section Sides

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem mem_bipA_iff (v : α ⊕ β) : v ∈ bipA α β ↔ ∃ c, v = Sum.inl c := by
  simp only [bipA, Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem mem_bipB_iff (v : α ⊕ β) : v ∈ bipB α β ↔ ∃ c, v = Sum.inr c := by
  simp only [bipB, Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

/-- A vertex of the `β`-side is not on the `α`-side. -/
theorem mem_bipB_imp_not_mem_bipA {v : α ⊕ β} (hB : v ∈ bipB α β) :
    ¬ (v ∈ bipA α β) := by
  rintro hA
  rcases mem_bipB_iff v |>.1 hB with ⟨c, hc⟩
  rcases mem_bipA_iff v |>.1 hA with ⟨d, hd⟩
  exact Sum.inl_ne_inr (hc.symm.trans hd).symm

/-- A vertex of the `α`-side is not on the `β`-side. -/
theorem mem_bipA_imp_not_mem_bipB {v : α ⊕ β} (hA : v ∈ bipA α β) :
    ¬ (v ∈ bipB α β) := by
  rintro hB
  rcases mem_bipA_iff v |>.1 hA with ⟨c, hc⟩
  rcases mem_bipB_iff v |>.1 hB with ⟨d, hd⟩
  exact Sum.inl_ne_inr (hc.symm.trans hd)

/-- Every vertex lies on one of the two sides. -/
theorem mem_bipA_or_mem_bipB (v : α ⊕ β) : v ∈ bipA α β ∨ v ∈ bipB α β := by
  cases v with
  | inl c =>
    exact Or.inl (show Sum.inl c ∈ bipA α β from
      Finset.mem_image_of_mem _ (Finset.mem_univ c))
  | inr c =>
    exact Or.inr (show Sum.inr c ∈ bipB α β from
      Finset.mem_image_of_mem _ (Finset.mem_univ c))

theorem card_bipA : (bipA α β).card = Fintype.card α := by
  rw [bipA, Finset.card_image_of_injective _ (Sum.inl_injective), Finset.card_univ]

/-- In `K_{α, β}` every adjacency joins the two sides. -/
theorem adj_bip (v w : α ⊕ β) :
    (completeBipartiteGraph α β).Adj v w ↔
      (v ∈ bipA α β ∧ w ∈ bipB α β) ∨ (v ∈ bipB α β ∧ w ∈ bipA α β) := by
  rcases v with (c | c) <;> rcases w with (d | d) <;>
    simp [completeBipartiteGraph_adj, bipA, bipB, Finset.mem_image]

end Sides

section BlockSides

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  [DecidableRel ((completeBipartiteGraph α β).Adj)]

/-- In the complete bipartite graph, a quadrilateral block has exactly two
vertices on the `α`-side: along the cycle `a - x - b - y - a` the antipodal
vertices `a, b` lie on the same side, `x, y` on the other. -/
theorem IsQuadBlock.card_A {s : Finset (α ⊕ β)}
    (hs : (completeBipartiteGraph α β).IsQuadBlock s) :
    (s ∩ bipA α β).card = 2 := by
  obtain ⟨a, b, x, y, hs4, hax, hab, hay, hbx, hxy, hby,
    e_ax, e_xb, e_by, e_ya⟩ := hs.exists_cycle_distinct
  have hmem : ∀ z ∈ ({a, x, b, y} : Finset (α ⊕ β)), z ∈ s := by
    intro z hz; rw [hs4]; exact hz
  -- Two vertices of the block on the `α`-side, no other, determine `s ∩ bipA`.
  have key : ∀ p q : α ⊕ β, p ∈ ({a, x, b, y} : Finset (α ⊕ β)) → p ∈ bipA α β →
      q ∈ ({a, x, b, y} : Finset (α ⊕ β)) → q ∈ bipA α β → p ≠ q →
      (∀ z ∈ ({a, x, b, y} : Finset (α ⊕ β)) \ {p, q}, z ∉ bipA α β) →
      s ∩ bipA α β = {p, q} := by
    intro p q hp hpA hq hqA hpq hnot
    refine Finset.Subset.antisymm (fun z hz => ?_) ?_
    · by_cases hz' : z ∈ ({p, q} : Finset (α ⊕ β))
      · exact hz'
      · have hmem' : z ∈ s \ ({p, q} : Finset (α ⊕ β)) :=
          Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.1 hz).1, hz'⟩
        rw [hs4] at hmem'
        exact absurd ((Finset.mem_inter.1 hz).2) (hnot _ hmem')
    · intro z hz
      rcases mem_pair z p q hz with hzp | hzq
      · rw [hzp]
        exact Finset.mem_inter.2 ⟨hmem p hp, hpA⟩
      · rw [hzq]
        exact Finset.mem_inter.2 ⟨hmem q hq, hqA⟩
  -- The sides of the four cycle vertices, in the order `a, x, b, y`.
  have hside : (a ∈ bipA α β ∧ x ∈ bipB α β ∧ b ∈ bipA α β ∧ y ∈ bipB α β) ∨
      (a ∈ bipB α β ∧ x ∈ bipA α β ∧ b ∈ bipB α β ∧ y ∈ bipA α β) := by
    rcases mem_bipA_or_mem_bipB a with haA | haB
    · have hxB : x ∈ bipB α β := by
        rcases (adj_bip a x).1 e_ax with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · exact absurd h1 (mem_bipA_imp_not_mem_bipB haA)
      have hyB : y ∈ bipB α β := by
        rcases (adj_bip y a).1 e_ya with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h2 (mem_bipA_imp_not_mem_bipB haA)
        · exact h1
      have hbA : b ∈ bipA α β := by
        rcases (adj_bip x b).1 e_xb with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1 (mem_bipB_imp_not_mem_bipA hxB)
        · exact h2
      exact Or.inl ⟨haA, hxB, hbA, hyB⟩
    · have hxA : x ∈ bipA α β := by
        rcases (adj_bip a x).1 e_ax with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1 (mem_bipB_imp_not_mem_bipA haB)
        · exact h2
      have hyA : y ∈ bipA α β := by
        rcases (adj_bip y a).1 e_ya with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h1
        · exact absurd h2 (mem_bipB_imp_not_mem_bipA haB)
      have hbB : b ∈ bipB α β := by
        rcases (adj_bip x b).1 e_xb with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · exact absurd h1 (mem_bipA_imp_not_mem_bipB hxA)
      exact Or.inr ⟨haB, hxA, hbB, hyA⟩
  rcases hside with ⟨haA, hxB, hbA, hyB⟩ | ⟨haB, hxA, hbB, hyA⟩
  · have hnotA : ∀ z ∈ ({a, x, b, y} : Finset (α ⊕ β)) \ {a, b}, z ∉ bipA α β := by
      intro z hz
      rcases Finset.mem_sdiff.mp hz with ⟨hz1, hz2⟩
      rcases mem_four z a x b y hz1 with h1 | h1 | h1 | h1
      · exact absurd hz2 (by simp [h1])
      · exact mem_bipB_imp_not_mem_bipA (h1 ▸ hxB)
      · exact absurd hz2 (by simp [h1])
      · exact mem_bipB_imp_not_mem_bipA (h1 ▸ hyB)
    have h1 : s ∩ bipA α β = {a, b} := key a b (by simp) haA (by simp) hbA hab hnotA
    rw [h1, Finset.card_pair hab]
  · have hnotA : ∀ z ∈ ({a, x, b, y} : Finset (α ⊕ β)) \ {x, y}, z ∉ bipA α β := by
      intro z hz
      rcases Finset.mem_sdiff.mp hz with ⟨hz1, hz2⟩
      rcases mem_four z a x b y hz1 with h1 | h1 | h1 | h1
      · exact mem_bipB_imp_not_mem_bipA (h1 ▸ haB)
      · exact absurd hz2 (by simp [h1])
      · exact mem_bipB_imp_not_mem_bipA (h1 ▸ hbB)
      · exact absurd hz2 (by simp [h1])
    have h2 : s ∩ bipA α β = {x, y} := key x y (by simp) hxA (by simp) hyA hxy hnotA
    rw [h2, Finset.card_pair hxy]

/-- In the complete bipartite graph, a quadrilateral block has exactly two
vertices on the `β`-side. -/
theorem IsQuadBlock.card_B {s : Finset (α ⊕ β)}
    (hs : (completeBipartiteGraph α β).IsQuadBlock s) :
    (s ∩ bipB α β).card = 2 := by
  obtain ⟨a, b, x, y, hs4, hax, hab, hay, hbx, hxy, hby,
    e_ax, e_xb, e_by, e_ya⟩ := hs.exists_cycle_distinct
  have hmem : ∀ z ∈ ({a, x, b, y} : Finset (α ⊕ β)), z ∈ s := by
    intro z hz; rw [hs4]; exact hz
  have key : ∀ p q : α ⊕ β, p ∈ ({a, x, b, y} : Finset (α ⊕ β)) → p ∈ bipB α β →
      q ∈ ({a, x, b, y} : Finset (α ⊕ β)) → q ∈ bipB α β → p ≠ q →
      (∀ z ∈ ({a, x, b, y} : Finset (α ⊕ β)) \ {p, q}, z ∉ bipB α β) →
      s ∩ bipB α β = {p, q} := by
    intro p q hp hpB hq hqB hpq hnot
    refine Finset.Subset.antisymm (fun z hz => ?_) ?_
    · by_cases hz' : z ∈ ({p, q} : Finset (α ⊕ β))
      · exact hz'
      · have hmem' : z ∈ s \ ({p, q} : Finset (α ⊕ β)) :=
          Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.1 hz).1, hz'⟩
        rw [hs4] at hmem'
        exact absurd ((Finset.mem_inter.1 hz).2) (hnot _ hmem')
    · intro z hz
      rcases mem_pair z p q hz with hzp | hzq
      · rw [hzp]
        exact Finset.mem_inter.2 ⟨hmem p hp, hpB⟩
      · rw [hzq]
        exact Finset.mem_inter.2 ⟨hmem q hq, hqB⟩
  have hside : (a ∈ bipA α β ∧ x ∈ bipB α β ∧ b ∈ bipA α β ∧ y ∈ bipB α β) ∨
      (a ∈ bipB α β ∧ x ∈ bipA α β ∧ b ∈ bipB α β ∧ y ∈ bipA α β) := by
    rcases mem_bipA_or_mem_bipB a with haA | haB
    · have hxB : x ∈ bipB α β := by
        rcases (adj_bip a x).1 e_ax with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · exact absurd h1 (mem_bipA_imp_not_mem_bipB haA)
      have hyB : y ∈ bipB α β := by
        rcases (adj_bip y a).1 e_ya with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h2 (mem_bipA_imp_not_mem_bipB haA)
        · exact h1
      have hbA : b ∈ bipA α β := by
        rcases (adj_bip x b).1 e_xb with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1 (mem_bipB_imp_not_mem_bipA hxB)
        · exact h2
      exact Or.inl ⟨haA, hxB, hbA, hyB⟩
    · have hxA : x ∈ bipA α β := by
        rcases (adj_bip a x).1 e_ax with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1 (mem_bipB_imp_not_mem_bipA haB)
        · exact h2
      have hyA : y ∈ bipA α β := by
        rcases (adj_bip y a).1 e_ya with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h1
        · exact absurd h2 (mem_bipB_imp_not_mem_bipA haB)
      have hbB : b ∈ bipB α β := by
        rcases (adj_bip x b).1 e_xb with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · exact absurd h1 (mem_bipA_imp_not_mem_bipB hxA)
      exact Or.inr ⟨haB, hxA, hbB, hyA⟩
  rcases hside with ⟨haA, hxB, hbA, hyB⟩ | ⟨haB, hxA, hbB, hyA⟩
  · have hnotB : ∀ z ∈ ({a, x, b, y} : Finset (α ⊕ β)) \ {x, y}, z ∉ bipB α β := by
      intro z hz
      rcases Finset.mem_sdiff.mp hz with ⟨hz1, hz2⟩
      rcases mem_four z a x b y hz1 with h1 | h1 | h1 | h1
      · exact mem_bipA_imp_not_mem_bipB (h1 ▸ haA)
      · exact absurd hz2 (by simp [h1])
      · exact mem_bipA_imp_not_mem_bipB (h1 ▸ hbA)
      · exact absurd hz2 (by simp [h1])
    have h1 : s ∩ bipB α β = {x, y} := key x y (by simp) hxB (by simp) hyB hxy hnotB
    rw [h1, Finset.card_pair hxy]
  · have hnotB : ∀ z ∈ ({a, x, b, y} : Finset (α ⊕ β)) \ {a, b}, z ∉ bipB α β := by
      intro z hz
      rcases Finset.mem_sdiff.mp hz with ⟨hz1, hz2⟩
      rcases mem_four z a x b y hz1 with h1 | h1 | h1 | h1
      · exact absurd hz2 (by simp [h1])
      · exact mem_bipA_imp_not_mem_bipB (h1 ▸ hxA)
      · exact absurd hz2 (by simp [h1])
      · exact mem_bipA_imp_not_mem_bipB (h1 ▸ hyA)
    have h2 : s ∩ bipB α β = {a, b} := key a b (by simp) haB (by simp) hbB hab hnotB
    rw [h2, Finset.card_pair hab]

end BlockSides

/-- A quadrilateral packing of `K_{α, β}` of cardinality `S.card` covers
exactly `2 · S.card` vertices of the `α`-side. -/
theorem card_A_of_quadPacking {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    [DecidableRel ((completeBipartiteGraph α β).Adj)]
    {S : Finset (Finset (α ⊕ β))}
    (hS : (completeBipartiteGraph α β).IsQuadPacking S) :
    (S.biUnion id ∩ bipA α β).card = 2 * S.card := by
  have hfam' : (S : Set (Finset (α ⊕ β))).PairwiseDisjoint
      (fun B : Finset (α ⊕ β) => B ∩ bipA α β) := by
    intro B hB C hC hne
    show Disjoint (B ∩ bipA α β) (C ∩ bipA α β)
    refine Finset.disjoint_left.2 fun z hzB hzC => ?_
    exact (Finset.disjoint_left.mp (hS.2 B hB C hC hne) (Finset.mem_inter.1 hzB).1)
      (Finset.mem_inter.1 hzC).1
  have heq : S.biUnion id ∩ bipA α β =
      S.biUnion (fun B => B ∩ bipA α β) := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_inter.mp hz with ⟨hzB, hzA⟩
      rcases Finset.mem_biUnion.mp hzB with ⟨B, hB, hzB'⟩
      exact Finset.mem_biUnion.mpr ⟨B, hB, Finset.mem_inter.mpr ⟨hzB', hzA⟩⟩
    · intro hz
      rcases Finset.mem_biUnion.mp hz with ⟨B, hB, hzB'⟩
      refine Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hzB').2⟩
      exact Finset.mem_biUnion.mpr ⟨B, hB, (Finset.mem_inter.mp hzB').1⟩
  calc (S.biUnion id ∩ bipA α β).card = ∑ B ∈ S, (B ∩ bipA α β).card := by
        rw [heq, Finset.card_biUnion hfam']
    _ = ∑ _B ∈ S, 2 := Finset.sum_congr rfl fun B hB => (hS.1 B hB).card_A
    _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Every quadrilateral packing of `K_{α, β}` uses at most `⌊|α| / 2⌋`
blocks.** -/
theorem card_le_card_A {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    [DecidableRel ((completeBipartiteGraph α β).Adj)]
    {S : Finset (Finset (α ⊕ β))}
    (hS : (completeBipartiteGraph α β).IsQuadPacking S) :
    2 * S.card ≤ Fintype.card α := by
  have hle : (S.biUnion id ∩ bipA α β).card ≤ (bipA α β).card :=
    Finset.card_le_card fun _ hz => (Finset.mem_inter.mp hz).2
  rw [card_A_of_quadPacking hS, card_bipA] at hle
  exact hle

/-- Disjoint quadrilaterals in `K_{2k-1, 2k+1}` are limited to `k - 1`. -/
theorem card_le_k_sub_one (k : ℕ) (hk : 1 ≤ k)
    {S : Finset (Finset (Fin (2 * k - 1) ⊕ Fin (2 * k + 1)))}
    (hS : (completeBipartiteGraph (Fin (2 * k - 1))
      (Fin (2 * k + 1))).IsQuadPacking S) :
    S.card ≤ k - 1 := by
  classical
  have hle := card_le_card_A (α := Fin (2 * k - 1)) (β := Fin (2 * k + 1))
    (S := S) hS
  rw [Fintype.card_fin] at hle
  omega

/-- **Sharpness of Wa10.** For `k ≥ 1` the complete bipartite graph
`K_{2k-1, 2k+1}` has `4k` vertices but no spanning quadrilateral factor, so
the minimum-degree hypothesis `δ(G) ≥ 2k` cannot be weakened to `2k - 1`. -/
theorem no_quadFactor_knm (k : ℕ) (hk : 1 ≤ k) :
    ¬ (completeBipartiteGraph (Fin (2 * k - 1)) (Fin (2 * k + 1))).HasQuadFactor := by
  classical
  rintro ⟨S, hS, hdisj, hcov⟩
  have hpack : (completeBipartiteGraph (Fin (2 * k - 1))
      (Fin (2 * k + 1))).IsQuadPacking S :=
    And.intro hS fun s hs t ht hne => And.intro (hdisj s hs t ht hne) hcov
  have hle := card_le_card_A (α := Fin (2 * k - 1)) (β := Fin (2 * k + 1))
    (S := S) hpack
  rw [Fintype.card_fin] at hle
  -- A factor covering all `4k` vertices has exactly `k` blocks.
  have hdisjS : (S : Set (Finset _)).PairwiseDisjoint id :=
    fun B hB C hC hne => hdisj B hB C hC hne
  have hcard : (S.biUnion id).card = 4 * S.card := by
    calc (S.biUnion id).card = ∑ B ∈ S, (id B).card := Finset.card_biUnion hdisjS
      _ = ∑ _B ∈ S, 4 := Finset.sum_congr rfl fun B hB => (hS B hB).1
      _ = 4 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hkey : 4 * S.card = 4 * k := by
    calc 4 * S.card = (S.biUnion id).card := hcard.symm
      _ = Fintype.card (Fin (2 * k - 1) ⊕ Fin (2 * k + 1)) := by
          rw [hcov, Finset.card_univ]
      _ = 4 * k := by rw [Fintype.card_sum, Fintype.card_fin]; omega
  omega

end SimpleGraph
