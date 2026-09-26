import JSP467.WDefs
import JSP467.WCover
import JSP467.Chord

/-!
# JSP-000467 — feasible-chain existence machinery

Wang's proof (Wa10) replaces the maximum-packing viewpoint by a *covering
chain* `(T, S, x₀)`: a triangle `T`, a quadrilateral packing `S` disjoint
from `T`, and a single terminal vertex `x₀`, together covering `V`.  When the
4-element leftover `U` of a cover carries a triangle, splitting `U` into
`T ∪ {x₀}` produces such a chain; when `U` carries a *paw* (a triangle plus a
pendant edge), the chain is even *strong*.

* `IsCover.chain_of_triangle` — a cover whose leftover contains a triangle
  yields a chain.
* `exists_feasibleChain` — chains live in the finite type
  `Finset V × Finset (Finset V) × V`, so a lexicographically maximal one
  (first `blockSum`, then the number of `K₄`-blocks) exists: a *feasible*
  chain in Wang's sense.
* `IsCover.strongChain_of_paw` — a paw on the leftover yields a strong chain.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- A cover whose leftover `U` contains a triangle `T` produces a chain: the
fourth vertex `x₀ ∈ U \ T` becomes the terminal vertex. -/
theorem IsCover.chain_of_triangle {S : Finset (Finset V)} {U T : Finset V}
    {x0 : V} (hc : G.IsCover S U) (hTsub : T ⊆ U) (hT : G.IsTriangle T)
    (hx0U : x0 ∈ U) (hx0T : x0 ∉ T) : G.IsChain T S x0 := by
  -- `U` is `T` plus the single extra vertex `x₀`.
  have hcard : (insert x0 T).card = U.card := by
    rw [Finset.card_insert_of_notMem hx0T, hT.1, hc.hcard]
  have hU : U = insert x0 T :=
    (Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hx0U hTsub) hcard.ge).symm
  refine ⟨hT, hc.hS, hc.hdisj.symm.mono_left hTsub, ?_, ?_⟩
  · intro h
    rcases Finset.mem_union.1 h with hT' | hS'
    · exact hx0T hT'
    · exact (Finset.disjoint_left.1 hc.hdisj) hS' hx0U
  · rw [← hc.hcover, hU]
    ext v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto

/-- Among all chains there is a lexicographically maximal one — first in
`blockSum` (twice the chord count `Σ τ`), then in the number of `K₄`-blocks —
i.e. a *feasible chain*.  The two maximisations are performed successively
over the finite set of chain triples `(T, S, x₀)`. -/
theorem exists_feasibleChain
    (h : ∃ T : Finset V, ∃ S : Finset (Finset V), ∃ x0 : V,
      G.IsChain T S x0) :
    ∃ T : Finset V, ∃ S : Finset (Finset V), ∃ x0 : V,
      G.IsFeasibleChain T S x0 := by
  classical
  set P : Finset (Finset V × Finset (Finset V) × V) :=
    univ.filter fun p => G.IsChain p.1 p.2.1 p.2.2 with hPdef
  have hmem : ∀ p : Finset V × Finset (Finset V) × V,
      p ∈ P ↔ G.IsChain p.1 p.2.1 p.2.2 := by
    intro p
    simp [hPdef]
  obtain ⟨T₀, S₀, x₀, h₀⟩ := h
  have hneP : P.Nonempty := ⟨(T₀, S₀, x₀), (hmem _).2 h₀⟩
  -- First maximise `blockSum`.
  obtain ⟨p, hpP, hpmax⟩ :=
    Finset.exists_max_image P (fun q => blockSum G q.2.1) hneP
  -- Then, among the `blockSum`-maximal chains, maximise the `K₄`-count.
  set Q : Finset (Finset V × Finset (Finset V) × V) :=
    P.filter fun q => blockSum G q.2.1 = blockSum G p.2.1 with hQdef
  have hmemQ : ∀ q : Finset V × Finset (Finset V) × V,
      q ∈ Q ↔ G.IsChain q.1 q.2.1 q.2.2 ∧
        blockSum G q.2.1 = blockSum G p.2.1 := by
    intro q
    simp [hQdef, hmem q]
  have hneQ : Q.Nonempty := ⟨p, (hmemQ p).2 ⟨(hmem p).1 hpP, rfl⟩⟩
  obtain ⟨q, hqQ, hqmax⟩ := Finset.exists_max_image Q
    (fun r => (r.2.1.filter fun B => edgeSum G B = 12).card) hneQ
  obtain ⟨hqchain, hqeq⟩ := (hmemQ q).1 hqQ
  refine ⟨q.1, q.2.1, q.2.2, hqchain, ?_, ?_⟩
  · intro T' S' x0' hch
    have hle : blockSum G S' ≤ blockSum G p.2.1 :=
      hpmax (T', S', x0') ((hmem _).2 hch)
    omega
  · intro T' S' x0' hch heq
    exact hqmax (T', S', x0')
      ((hmemQ _).2 ⟨hch, heq.trans hqeq⟩)

omit [DecidableRel G.Adj] in
/-- A cover whose leftover `U` carries a paw — a triangle `T ⊆ U` with the
fourth vertex `x₀` pendant on `x₁ ∈ T` — yields a strong chain `(T, S, x₀)`
with pendant edge `x₀x₁`. -/
theorem IsCover.strongChain_of_paw {S : Finset (Finset V)} {U : Finset V}
    (hc : G.IsCover S U) (hpaw : G.IsPaw U) :
    ∃ T : Finset V, ∃ x0 : V, G.IsStrongChain T S x0 := by
  obtain ⟨T, x0, x1, hT, hTsub, hx0U, hx0T, hx1T, hadj, -⟩ := hpaw
  exact ⟨T, x0, hc.chain_of_triangle hTsub hT hx0U hx0T, x1, hx1T, hadj⟩

end SimpleGraph
