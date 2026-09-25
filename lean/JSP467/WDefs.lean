import JSP467.Main
import JSP467.Chord

/-!
# JSP-000467 — Wang's feasible-chain definitions (Wa10)

Wang's proof of the Erdős–Faudree conjecture does not enlarge packings.  It
works with a covering *chain* `(T, Q₁, …, Q_{k-1})` — a triangle `T`, `k - 1`
disjoint quadrilaterals, and a single *terminal point* `x₀` — chosen
lexicographically maximal in `(Σ τ(Qᵢ), #{i : τ(Qᵢ) = 2})`, plus a *strong*
variant `(x₀x₁, T, Q₁, …, Q_{k-1})` with `x₀x₁ ∈ E`, `x₁ ∈ T`.

This file contains the definitions; existence and the local switching claims
live in the `W*` modules downstream.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- A 3-element set of pairwise-adjacent vertices: a triangle `C₃`. -/
def IsTriangle (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → G.Adj x y

/-- A *chain* `(T, S, x₀)`: a triangle `T`, a quadrilateral packing `S`
disjoint from `T`, and a terminal vertex `x₀`, together covering `V`. -/
structure IsChain (T : Finset V) (S : Finset (Finset V)) (x0 : V) : Prop where
  hT : G.IsTriangle T
  hS : G.IsQuadPacking S
  hTS : Disjoint T (S.biUnion id)
  hx0 : x0 ∉ T ∪ S.biUnion id
  hcov : T ∪ S.biUnion id ∪ {x0} = Finset.univ

/-- A *strong* chain `(x₀x₁, T, S)`: a chain whose terminal vertex `x₀` is
adjacent to some `x₁ ∈ T`. -/
def IsStrongChain (T : Finset V) (S : Finset (Finset V)) (x0 : V) : Prop :=
  G.IsChain T S x0 ∧ ∃ x1 ∈ T, G.Adj x0 x1

/-- The chord-count of a chain (Wang's `Σ τ(Qᵢ)`, here as `blockSum` which is
twice the chord sum). -/
abbrev chainSum (S : Finset (Finset V)) [DecidableRel G.Adj] : ℕ :=
  blockSum G S

/-- A *feasible chain*: a chain lexicographically maximal in `(Σ τ, #K₄-blocks)`
among all chains of `G`.  Here `#K₄-blocks` is counted by blocks whose induced
subgraph is the full `K₄` (`edgeSum = 12`). -/
def IsFeasibleChain (T : Finset V) (S : Finset (Finset V)) (x0 : V)
    [DecidableRel G.Adj] : Prop :=
  G.IsChain T S x0 ∧
    (∀ T' : Finset V, ∀ S' : Finset (Finset V), ∀ x0' : V,
      G.IsChain T' S' x0' → blockSum G S' ≤ blockSum G S) ∧
    (∀ T' : Finset V, ∀ S' : Finset (Finset V), ∀ x0' : V,
      G.IsChain T' S' x0' → blockSum G S' = blockSum G S →
        (S'.filter fun B => edgeSum G B = 12).card ≤
          (S.filter fun B => edgeSum G B = 12).card)

/-- A *strong feasible chain* (Wang's `σ = (x₀x₁, T, Q₁, …, Q_{k-1})`). -/
def IsStrongFeasibleChain (T : Finset V) (S : Finset (Finset V)) (x0 : V)
    [DecidableRel G.Adj] : Prop :=
  G.IsFeasibleChain T S x0 ∧ ∃ x1 ∈ T, G.Adj x0 x1

end SimpleGraph
