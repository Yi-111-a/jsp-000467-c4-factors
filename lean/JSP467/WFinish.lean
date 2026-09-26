import JSP467.WChain
import JSP467.WCount
import JSP467.WPigeon

/-!
# JSP-000467 — the terminal charge count (Wang's `2e(x₀,Q) + e(x₂x₃,Q) ≥ 9`)

The final counting step of Wang's proof (Wa10).  In a *strong* chain
`(T, S, x₀)` — with `x₁ ∈ T` the unique neighbour of `x₀` inside `T`
(the pendant edge `x₀x₁`) and `T = {x₁, x₂, x₃}` — the weighted charge

    `2 * crossEdges G {x0} Q + crossEdges G {x2, x3} Q`

sums, over the `k - 1` blocks `Q ∈ S`, to at least `8k - 6`.  Since
`8k - 6 > 8 (k - 1)`, some block carries charge at least `9`.

* `crossEdges_singleton`, `crossEdges_pair` — the count from a one- or
  two-element set is the (sum of) neighbourhood counts.
* `IsChain.biUnion_eq` — the block union is `univ \ (T ∪ {x₀})`.
* `IsChain.card_quads` — a chain on `4k` vertices has `k - 1` blocks.
* `neighbor_biUnion_card_ge` — degree-split bound: a vertex whose
  neighbours inside `T ∪ {x₀}` fit in an `m`-element set sends at least
  `2k - m` edges into the blocks.
* `terminal_charge_sum` — the total charge is `≥ 8k - 6`.
* `exists_quad_charge_ge_nine` — pigeonhole: some `Q ∈ S` carries
  charge `≥ 9`.

All statements are over an ambient `SimpleGraph V` with
`[DecidableRel G.Adj]`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- In a chain `(T, S, x₀)` the union of the packing blocks is exactly
`univ \ (T ∪ {x₀})`. -/
theorem IsChain.biUnion_eq {T : Finset V} {S : Finset (Finset V)} {x0 : V}
    (hc : G.IsChain T S x0) :
    S.biUnion id = Finset.univ \ (T ∪ {x0}) := by
  have hx0S : x0 ∉ S.biUnion id :=
    fun h => hc.hx0 (Finset.mem_union.2 (Or.inr h))
  apply Finset.Subset.antisymm
  · intro y hy
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_univ y, fun hcon => ?_⟩
    rcases Finset.mem_union.1 hcon with hT | hx
    · exact Finset.disjoint_left.1 hc.hTS hT hy
    · exact hx0S (Finset.mem_singleton.1 hx ▸ hy)
  · intro y hy
    have hy' : y ∉ T ∪ {x0} := (Finset.mem_sdiff.1 hy).2
    have hyu : y ∈ T ∪ S.biUnion id ∪ {x0} := by
      rw [hc.hcov]; exact Finset.mem_univ y
    rcases Finset.mem_union.1 hyu with h | h
    · rcases Finset.mem_union.1 h with hT | hS
      · exact absurd hT (fun hh => hy' (Finset.mem_union.2 (Or.inl hh)))
      · exact hS
    · exact absurd h (fun hh => hy' (Finset.mem_union.2 (Or.inr hh)))

omit [DecidableRel G.Adj] in
/-- A chain on `4k` vertices has `k - 1` quadrilateral blocks. -/
theorem IsChain.card_quads {T : Finset V} {S : Finset (Finset V)} {x0 : V}
    (hc : G.IsChain T S x0) {k : ℕ} (hcard : Fintype.card V = 4 * k) :
    S.card + 1 = k := by
  have hdisj : (S : Set (Finset V)).PairwiseDisjoint id :=
    fun B hB C hC hne => hc.hS.2 B hB C hC hne
  have hScard : (S.biUnion id).card = 4 * S.card := by
    calc (S.biUnion id).card
        = ∑ B ∈ S, (id B).card := Finset.card_biUnion hdisj
      _ = ∑ _B ∈ S, 4 :=
          Finset.sum_congr rfl fun B hB => (hc.hS.1 B hB).1
      _ = 4 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have huniv : (T ∪ S.biUnion id ∪ {x0}).card = 4 * k := by
    rw [hc.hcov, Finset.card_univ, hcard]
  have hd1 : Disjoint (T ∪ S.biUnion id) {x0} :=
    Finset.disjoint_singleton_right.2 hc.hx0
  rw [Finset.card_union_of_disjoint hd1,
    Finset.card_union_of_disjoint hc.hTS, hc.hT.1, Finset.card_singleton,
    hScard] at huniv
  omega

/-- **Degree-split bound.**  If the neighbours of `v` inside `T ∪ {x₀}`
are contained in a set `A` of at most `m` vertices, then `v` has at
least `2k - m` neighbours inside the block union `⋃S` (written as
`2k ≤ m + |⋃S ∩ N(v)|` to stay in `ℕ`). -/
theorem neighbor_biUnion_card_ge {T : Finset V} {S : Finset (Finset V)}
    {x0 v : V} (hc : G.IsChain T S x0) {k m : ℕ} {A : Finset V}
    (hdeg : 2 * k ≤ G.minDegree)
    (hsub : (T ∪ {x0}) ∩ G.neighborFinset v ⊆ A) (hm : A.card ≤ m) :
    2 * k ≤ m + (S.biUnion id ∩ G.neighborFinset v).card := by
  have huniv : Finset.univ = (T ∪ {x0}) ∪ S.biUnion id := by
    rw [← hc.hcov]
    ext y
    simp only [Finset.mem_union, Finset.mem_singleton]
    tauto
  have hdisj : Disjoint (T ∪ {x0}) (S.biUnion id) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hc.hTS, Finset.disjoint_singleton_left.2
      (fun h => hc.hx0 (Finset.mem_union.2 (Or.inr h)))⟩
  have hd : Disjoint ((T ∪ {x0}) ∩ G.neighborFinset v)
      (S.biUnion id ∩ G.neighborFinset v) :=
    Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hdisj
  have hNvcard : (G.neighborFinset v).card =
      ((T ∪ {x0}) ∩ G.neighborFinset v).card +
        (S.biUnion id ∩ G.neighborFinset v).card := by
    conv_lhs => rw [← Finset.univ_inter (G.neighborFinset v), huniv,
      Finset.union_inter_distrib_right, Finset.card_union_of_disjoint hd]
  have hdeg' : 2 * k ≤ (G.neighborFinset v).card :=
    hdeg.trans ((G.minDegree_le_degree v).trans
      (le_of_eq (G.card_neighborFinset_eq_degree v).symm))
  have hle : ((T ∪ {x0}) ∩ G.neighborFinset v).card ≤ m :=
    (Finset.card_le_card hsub).trans hm
  omega

/-- **Terminal charge bound.**  In a strong chain with `x₁` the unique
neighbour of `x₀` inside `T = {x₁,x₂,x₃}`: the neighbours of `x₀` inside
`T ∪ {x₀}` number at most `1` (`⊆ {x₁}`), and those of `x₂`, `x₃` at
most `2` each (`⊆ {x₁,x₃}` and `{x₁,x₂}` — note `x₀` is *not* adjacent
to `x₂`, `x₃` by the pendant hypothesis).  Hence

    `2 * e(x₀, ⋃S) + e({x₂,x₃}, ⋃S) ≥ 2(2k-1) + 2(2k-2) = 8k - 6`. -/
theorem terminal_charge_sum {T : Finset V} {S : Finset (Finset V)}
    {x0 x1 x2 x3 : V} (hc : G.IsChain T S x0) {k : ℕ}
    (_hcard : Fintype.card V = 4 * k) (hdeg : 2 * k ≤ G.minDegree)
    (hx1 : x1 ∈ T) (_hadj : G.Adj x0 x1)
    (hpend : ∀ y ∈ T, G.Adj x0 y → y = x1)
    (hx2 : x2 ∈ T) (hx3 : x3 ∈ T)
    (h23 : x2 ≠ x3) (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) :
    8 * k - 6 ≤ 2 * crossEdges G {x0} (S.biUnion id) +
      crossEdges G {x2, x3} (S.biUnion id) := by
  -- `T` is exactly the three-element set `{x1, x2, x3}`.
  have hTsub : ({x1, x2, x3} : Finset V) ⊆ T := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact hx1
    · exact hx2
    · exact hx3
  have hcard3 : ({x1, x2, x3} : Finset V).card = 3 := by
    have hx1nin : x1 ∉ ({x2, x3} : Finset V) := by
      simp [h12, h13]
    rw [Finset.card_insert_of_notMem hx1nin, Finset.card_pair h23]
  have hTeq : T = {x1, x2, x3} :=
    (Finset.eq_of_subset_of_card_le hTsub
      (le_of_eq (hc.hT.1.trans hcard3.symm))).symm
  -- Neighbours of `x₀` inside `T ∪ {x₀}` are contained in `{x₁}`.
  have hsub0 : (T ∪ {x0}) ∩ G.neighborFinset x0 ⊆ {x1} := by
    intro y hy
    rw [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton,
      G.mem_neighborFinset] at hy
    rw [Finset.mem_singleton]
    rcases hy with ⟨hT' | hyx0, h0⟩
    · exact hpend y hT' h0
    · exact absurd (hyx0 ▸ h0) G.irrefl
  have hb0 : 2 * k ≤ 1 + (S.biUnion id ∩ G.neighborFinset x0).card :=
    neighbor_biUnion_card_ge hc hdeg hsub0
      (le_of_eq (Finset.card_singleton x1))
  -- Neighbours of `x₂` inside `T ∪ {x₀}` are contained in `{x₁, x₃}`.
  have hsub2 : (T ∪ {x0}) ∩ G.neighborFinset x2 ⊆ {x1, x3} := by
    intro y hy
    rw [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton,
      G.mem_neighborFinset] at hy
    rw [Finset.mem_insert, Finset.mem_singleton]
    obtain ⟨hmem, h2⟩ := hy
    rcases hmem with hT' | hyx0
    · have hyT : y ∈ ({x1, x2, x3} : Finset V) := hTeq ▸ hT'
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hyT
      rcases hyT with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd h2 G.irrefl
      · exact Or.inr rfl
    · exfalso
      have h20 : G.Adj x0 x2 := (hyx0 ▸ h2).symm
      exact h12 (hpend x2 hx2 h20).symm
  have hb2 : 2 * k ≤ 2 + (S.biUnion id ∩ G.neighborFinset x2).card :=
    neighbor_biUnion_card_ge hc hdeg hsub2
      (le_of_eq (Finset.card_pair h13))
  -- Neighbours of `x₃` inside `T ∪ {x₀}` are contained in `{x₁, x₂}`.
  have hsub3 : (T ∪ {x0}) ∩ G.neighborFinset x3 ⊆ {x1, x2} := by
    intro y hy
    rw [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton,
      G.mem_neighborFinset] at hy
    rw [Finset.mem_insert, Finset.mem_singleton]
    obtain ⟨hmem, h3⟩ := hy
    rcases hmem with hT' | hyx0
    · have hyT : y ∈ ({x1, x2, x3} : Finset V) := hTeq ▸ hT'
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hyT
      rcases hyT with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd h3 G.irrefl
    · exfalso
      have h30 : G.Adj x0 x3 := (hyx0 ▸ h3).symm
      exact h13 (hpend x3 hx3 h30).symm
  have hb3 : 2 * k ≤ 2 + (S.biUnion id ∩ G.neighborFinset x3).card :=
    neighbor_biUnion_card_ge hc hdeg hsub3
      (le_of_eq (Finset.card_pair h12))
  rw [crossEdges_singleton, crossEdges_pair h23]
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Small pigeonhole: if `∑ Q ∈ S, f Q > |S| * c` then some `Q ∈ S`
satisfies `c < f Q`. -/
theorem exists_charge_ge {S : Finset (Finset V)} {f : Finset V → ℕ}
    {c : ℕ} (h : S.card * c < ∑ Q ∈ S, f Q) :
    ∃ Q ∈ S, c < f Q := by
  by_contra hcon
  have hle : ∀ Q ∈ S, f Q ≤ c :=
    fun Q hQ => le_of_not_gt fun hlt => hcon ⟨Q, hQ, hlt⟩
  have hsum : ∑ Q ∈ S, f Q ≤ S.card * c :=
    calc ∑ Q ∈ S, f Q
        ≤ ∑ _Q ∈ S, c := Finset.sum_le_sum hle
      _ = S.card * c := by rw [Finset.sum_const, smul_eq_mul]
  omega

/-- **Wang's `9`-charge block.**  The charges
`2 * e(x₀, Q) + e({x₂,x₃}, Q)` sum to `≥ 8k - 6 > 8 * (k - 1)` over the
`k - 1` blocks, so some `Q ∈ S` carries charge at least `9`. -/
theorem exists_quad_charge_ge_nine {T : Finset V} {S : Finset (Finset V)}
    {x0 x1 x2 x3 : V} (hc : G.IsChain T S x0) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : 2 * k ≤ G.minDegree)
    (hx1 : x1 ∈ T) (hadj : G.Adj x0 x1)
    (hpend : ∀ y ∈ T, G.Adj x0 y → y = x1)
    (hx2 : x2 ∈ T) (hx3 : x3 ∈ T)
    (h23 : x2 ≠ x3) (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) :
    ∃ Q ∈ S, 9 ≤ 2 * crossEdges G {x0} Q + crossEdges G {x2, x3} Q := by
  have hScard : S.card + 1 = k := hc.card_quads hcard
  have hlb : 8 * k - 6 ≤ 2 * crossEdges G {x0} (S.biUnion id) +
      crossEdges G {x2, x3} (S.biUnion id) :=
    terminal_charge_sum hc hcard hdeg hx1 hadj hpend hx2 hx3 h23 h12 h13
  have hdisj : (S : Set (Finset V)).PairwiseDisjoint id :=
    fun B hB C hC hne => hc.hS.2 B hB C hC hne
  have hsum : ∑ Q ∈ S,
      (2 * crossEdges G {x0} Q + crossEdges G {x2, x3} Q)
      = 2 * crossEdges G {x0} (S.biUnion id) +
        crossEdges G {x2, x3} (S.biUnion id) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      sum_crossEdges_biUnion hdisj, sum_crossEdges_biUnion hdisj]
  obtain ⟨Q, hQ, hlt⟩ := exists_charge_ge (S := S)
    (f := fun Q => 2 * crossEdges G {x0} Q + crossEdges G {x2, x3} Q)
    (c := 8) (by rw [hsum]; omega)
  exact ⟨Q, hQ, by omega⟩

end SimpleGraph
