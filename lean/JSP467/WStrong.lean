import JSP467.WChain
import JSP467.WCount
import JSP467.WCover
import JSP467.WClass

/-!
# JSP-000467 — Wang's Claim 2.1: strong chains and terminal cross-edges

The opening move of Wang's Claim 2.1 (Wa10): among all *feasible* chains
`(T, S, x₀)` of a `4k`-vertex graph with `δ(G) ≥ 2k`, choose one maximising
the number `m` of edges from the terminal vertex `x₀` into a single
quadrilateral block.  Then either `x₀` already sees the triangle `T` (the
chain is *strong*), or all `≥ 2k` neighbours of `x₀` lie in the `k - 1`
blocks of `S`, and the pigeonhole `2k > 2(k - 1)` produces a block `B ∈ S`
with `3 ≤ crossEdges G {x0} B`.

* `chain_card` — a chain on `4k` vertices has `k - 1` blocks.
* `crossEdges_singleton` — cross edges from `{x0}` are `x0`'s neighbours
  in `B`.
* `exists_feasibleChain_maxTerminal` — a feasible chain maximising
  `S.sup (fun B => crossEdges G {x0} B)` exists (the `sup` defaults to `0`
  on the empty packing, so no nonemptiness side-condition is needed).
* `strong_or_three_seer` — the Claim-2.1 dichotomy.
* `exists_strongFeasible_or_terminal3` — packaged version from chain
  existence alone.

All statements are over an ambient `SimpleGraph V` with
`[DecidableRel G.Adj]`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- **Counting.**  A chain `(T, S, x₀)` on `4k` vertices consists of the
triangle `T` (3 vertices), the terminal `x₀` (1 vertex), and `S`'s disjoint
4-vertex blocks, so `S.card = k - 1`. -/
theorem chain_card {T : Finset V} {S : Finset (Finset V)} {x0 : V}
    (hc : G.IsChain T S x0) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hk : 2 ≤ k) : S.card = k - 1 := by
  have hdisj : (S : Set (Finset V)).PairwiseDisjoint id :=
    fun B hB C hC hne => hc.hS.2 B hB C hC hne
  have hScard : (S.biUnion id).card = 4 * S.card := by
    calc (S.biUnion id).card
        = ∑ B ∈ S, (id B).card := Finset.card_biUnion hdisj
      _ = ∑ _B ∈ S, 4 := Finset.sum_congr rfl fun B hB => (hc.hS.1 B hB).1
      _ = 4 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hx0disj : Disjoint (T ∪ S.biUnion id) {x0} :=
    Finset.disjoint_singleton_right.2 hc.hx0
  have htot : (T ∪ S.biUnion id ∪ {x0}).card = Fintype.card V := by
    rw [hc.hcov, Finset.card_univ]
  rw [Finset.card_union_of_disjoint hx0disj,
    Finset.card_union_of_disjoint hc.hTS, hc.hT.1, hScard,
    Finset.card_singleton] at htot
  rw [hcard] at htot
  omega

/-- **Maximal terminal block.**  Among all feasible chains there is one
maximising `S.sup (fun B => crossEdges G {x0} B)` — the largest number of
edges from `x₀` into a single block of `S` (Wang's `m` in Claim 2.1). -/
theorem exists_feasibleChain_maxTerminal
    (h : ∃ T : Finset V, ∃ S : Finset (Finset V), ∃ x0 : V,
      G.IsChain T S x0) :
    ∃ T : Finset V, ∃ S : Finset (Finset V), ∃ x0 : V,
      G.IsFeasibleChain T S x0 ∧
        ∀ T' : Finset V, ∀ S' : Finset (Finset V), ∀ x0' : V,
          G.IsFeasibleChain T' S' x0' →
            S'.sup (fun B => crossEdges G {x0'} B) ≤
              S.sup (fun B => crossEdges G {x0} B) := by
  classical
  obtain ⟨T₀, S₀, x₀, h₀⟩ := exists_feasibleChain h
  set Q : Finset (Finset V × Finset (Finset V) × V) :=
    univ.filter fun p => G.IsFeasibleChain p.1 p.2.1 p.2.2 with hQdef
  have hmemQ : ∀ q : Finset V × Finset (Finset V) × V,
      q ∈ Q ↔ G.IsFeasibleChain q.1 q.2.1 q.2.2 := by
    intro q
    simp [hQdef]
  have hneQ : Q.Nonempty := ⟨(T₀, S₀, x₀), (hmemQ _).2 h₀⟩
  obtain ⟨p, hpQ, hpmax⟩ := Finset.exists_max_image Q
    (fun q => q.2.1.sup fun B => crossEdges G {q.2.2} B) hneQ
  exact ⟨p.1, p.2.1, p.2.2, (hmemQ p).1 hpQ,
    fun T' S' x0' h' => hpmax (T', S', x0') ((hmemQ _).2 h')⟩

/-- **Claim 2.1 dichotomy.**  In a `4k`-vertex graph with `δ(G) ≥ 2k`, a
feasible chain `(T, S, x₀)` is either *strong* (`x₀` sees `T`), or `x₀`'s
`≥ 2k` neighbours all lie among the `k - 1` blocks of `S`, and pigeonhole
yields a block `B ∈ S` receiving at least three edges from `x₀`. -/
theorem strong_or_three_seer {T : Finset V} {S : Finset (Finset V)} {x0 : V}
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hk : 2 ≤ k)
    (hmin : 2 * k ≤ G.minDegree) (hfeas : G.IsFeasibleChain T S x0) :
    G.IsStrongChain T S x0 ∨ ∃ B ∈ S, 3 ≤ crossEdges G {x0} B := by
  obtain ⟨hchain, -, -⟩ := hfeas
  by_cases hstrong : ∃ x1 ∈ T, G.Adj x0 x1
  · exact Or.inl ⟨hchain, hstrong⟩
  · refine Or.inr ?_
    push Not at hstrong
    -- Every neighbour of `x₀` lies in `⋃ S`: not in `T` (by `hstrong`) and
    -- not equal to `x₀` itself.
    have hsub : G.neighborFinset x0 ⊆ S.biUnion id := by
      intro y hy
      have hyadj : G.Adj x0 y := (G.mem_neighborFinset x0 y).1 hy
      have hyu : y ∈ T ∪ S.biUnion id ∪ {x0} := by
        rw [hchain.hcov]
        exact Finset.mem_univ y
      rcases Finset.mem_union.1 hyu with h | h
      · rcases Finset.mem_union.1 h with hT | hS
        · exact absurd hyadj (hstrong y hT)
        · exact hS
      · exact absurd (Finset.mem_singleton.1 h).symm (G.ne_of_adj hyadj)
    have hceq : crossEdges G {x0} (S.biUnion id) =
        (G.neighborFinset x0).card := by
      rw [crossEdges_singleton, Finset.inter_eq_right.2 hsub]
    have hlb : 2 * k ≤ crossEdges G {x0} (S.biUnion id) := by
      rw [hceq, G.card_neighborFinset_eq_degree]
      exact le_trans hmin (G.minDegree_le_degree x0)
    have hScard : S.card = k - 1 := chain_card hchain hcard hk
    have hdisj : (S : Set (Finset V)).PairwiseDisjoint id :=
      fun B hB C hC hne => hchain.hS.2 B hB C hC hne
    refine exists_crossEdges_ge hdisj (r := 3) ?_
    rw [hScard]
    -- `(k - 1) * 2 < 2 * k` since `2 ≤ k`.
    omega

/-- **Packaged opening move.**  From the existence of a chain, either a
*strong feasible* chain exists, or there is a feasible chain which is
maximal for the terminal cross-edge count and has a block `B ∈ S` with
`3 ≤ crossEdges G {x0} B`. -/
theorem exists_strongFeasible_or_terminal3 {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hk : 2 ≤ k)
    (hmin : 2 * k ≤ G.minDegree)
    (h : ∃ T : Finset V, ∃ S : Finset (Finset V), ∃ x0 : V,
      G.IsChain T S x0) :
    (∃ T : Finset V, ∃ S : Finset (Finset V), ∃ x0 : V,
      G.IsStrongFeasibleChain T S x0) ∨
    ∃ T : Finset V, ∃ S : Finset (Finset V), ∃ x0 : V,
      G.IsFeasibleChain T S x0 ∧
        (∀ T' : Finset V, ∀ S' : Finset (Finset V), ∀ x0' : V,
          G.IsFeasibleChain T' S' x0' →
            S'.sup (fun B => crossEdges G {x0'} B) ≤
              S.sup (fun B => crossEdges G {x0} B)) ∧
        ∃ B ∈ S, 3 ≤ crossEdges G {x0} B := by
  obtain ⟨T, S, x0, hfeas, hmax⟩ := exists_feasibleChain_maxTerminal h
  rcases strong_or_three_seer hcard hk hmin hfeas with hstrong | h3
  · exact Or.inl ⟨T, S, x0, hfeas, hstrong.2⟩
  · exact Or.inr ⟨T, S, x0, hfeas, hmax, h3⟩

end SimpleGraph
