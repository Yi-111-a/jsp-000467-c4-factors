import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.VecNotation

/-!
# JSP-000467 — definitions and quadrilateral-block API

Shared definitions for the Wang (Wa10) formalization: quadrilateral blocks
(`IsQuadBlock`), spanning quadrilateral factors (`HasQuadFactor`), and the
elementary API for building and combining blocks.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- A 4-element vertex set `s` is a *quadrilateral block* of `G` when the
subgraph induced by `s` contains a copy of `C₄` (necessarily spanning `s`,
since `s` has exactly four vertices).  The copy need not be induced: a block
may carry extra edges (e.g. `K₄` is a quadrilateral block). -/
def IsQuadBlock (s : Finset V) : Prop :=
  s.card = 4 ∧ Nonempty ((cycleGraph 4).Copy (G.induce (s : Set V)))

/-- `G` has a *spanning quadrilateral factor*: a family of pairwise-disjoint
quadrilateral blocks covering every vertex. -/
def HasQuadFactor : Prop :=
  ∃ S : Finset (Finset V),
    (∀ s ∈ S, G.IsQuadBlock s) ∧
    (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Disjoint s t) ∧
    S.biUnion id = Finset.univ

variable {G}

/-- Constructor: four distinct vertices carrying a cyclic 4-edge pattern
`a - b - c - d - a` inside `s = {a, b, c, d}` make `s` a quadrilateral block. -/
theorem IsQuadBlock.of_cycle {s : Finset V} {a b c d : V}
    (hs : s = {a, b, c, d})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (e1 : G.Adj a b) (e2 : G.Adj b c) (e3 : G.Adj c d) (e4 : G.Adj d a) :
    G.IsQuadBlock s := by
  have hcard : s.card = 4 := by
    rw [hs]
    simp [hab, hac, had, hbc, hbd, hcd]
  have hmem : ∀ i : Fin 4, ![a, b, c, d] i ∈ (↑s : Set V) := by
    intro i
    fin_cases i <;> simp [hs]
  have e1' : G.Adj b a := e1.symm
  have e2' : G.Adj c b := e2.symm
  have e3' : G.Adj d c := e3.symm
  have e4' : G.Adj a d := e4.symm
  refine ⟨hcard, ⟨⟨⟨fun i => ⟨![a, b, c, d] i, hmem i⟩, ?_⟩, ?_⟩⟩⟩
  · rintro i j h
    rw [induce_adj]
    rw [cycleGraph_adj'] at h
    fin_cases i <;> fin_cases j <;> simp_all <;> exact absurd h (by decide)
  · intro i j hij
    have h' : ![a, b, c, d] i = ![a, b, c, d] j := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Monotonicity: a quadrilateral block stays a block in any supergraph. -/
theorem IsQuadBlock.mono {H : SimpleGraph V} (hGH : G ≤ H) {s : Finset V}
    (hs : G.IsQuadBlock s) : H.IsQuadBlock s := by
  obtain ⟨hc, ⟨f⟩⟩ := hs
  refine ⟨hc, ⟨?_⟩⟩
  let g : G.induce (↑s : Set V) →g H.induce (↑s : Set V) := ⟨id, fun h => hGH h⟩
  refine (g.comp f.toHom).toCopy ?_
  intro x y hxy
  exact f.injective' hxy

/-- One quadrilateral block covering all vertices is a quad factor. -/
theorem HasQuadFactor.of_block_eq_univ {s : Finset V} (hs : s = Finset.univ)
    (h : G.IsQuadBlock s) : G.HasQuadFactor := by
  refine ⟨{s}, ?_, ?_, ?_⟩
  · intro t ht
    rw [Finset.mem_singleton.1 ht]
    exact h
  · intro t₁ h₁ t₂ h₂ hne
    simp only [Finset.mem_singleton] at h₁ h₂
    exact absurd (h₁.trans h₂.symm) hne
  · simp [hs]

/-- Adding a fresh disjoint block to a quad factor on the remaining vertices. -/
theorem HasQuadFactor.insert_block {s : Finset V} {S : Finset (Finset V)}
    (hs : G.IsQuadBlock s)
    (hcov : s ∪ S.biUnion id = Finset.univ)
    (hblk : ∀ t ∈ S, G.IsQuadBlock t)
    (hpair : ∀ t₁ ∈ S, ∀ t₂ ∈ S, t₁ ≠ t₂ → Disjoint t₁ t₂)
    (hdis : ∀ t ∈ S, Disjoint s t) :
    G.HasQuadFactor := by
  refine ⟨insert s S, ?_, ?_, ?_⟩
  · intro t ht
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hs
    · exact hblk t ht
  · intro t₁ h₁ t₂ h₂ hne
    rcases Finset.mem_insert.1 h₁ with rfl | h₁mem
    · rcases Finset.mem_insert.1 h₂ with rfl | h₂mem
      · exact absurd rfl hne
      · exact hdis t₂ h₂mem
    · rcases Finset.mem_insert.1 h₂ with rfl | h₂mem
      · exact (hdis t₁ h₁mem).symm
      · exact hpair t₁ h₁mem t₂ h₂mem hne
  · rw [Finset.biUnion_insert]
    exact hcov

end SimpleGraph
