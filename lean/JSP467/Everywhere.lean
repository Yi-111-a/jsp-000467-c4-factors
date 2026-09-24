import JSP467.Through

/-!
# JSP-000467 — every vertex lies on a quadrilateral block (k ≥ 2)

Instantiation of the pigeonhole lemma `exists_isQuadBlock_self` at the
Wang parameters `d = 2k`, `|V| = 4k`: the condition `4k < 2k(2k-1) + 1`
holds exactly when `k ≥ 2`, so every vertex of a `4k`-vertex graph with
`δ ≥ 2k` lies on some quadrilateral block whenever `k ≥ 2`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For `k ≥ 2`, every vertex of a graph on `4k` vertices with minimum
degree at least `2k` is contained in a quadrilateral block. -/
theorem exists_isQuadBlock_self_of_minDegree (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (hk : 2 ≤ k)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree) (v : V) :
    ∃ s : Finset V, G.IsQuadBlock s ∧ v ∈ s := by
  refine G.exists_isQuadBlock_self v hmin ?_
  rw [hcard]
  have h4 : 4 * k ≤ 2 * k * (2 * k - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  exact h4.trans_lt (Nat.lt_succ_self _)

end SimpleGraph
