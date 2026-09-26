import JSP467.WCover
import JSP467.CommonNbr

/-!
# JSP-000467 — the `C₃ + C₄` bridge: from covers to chains (Wa10)

In Wang's proof a key step is the observation that when a vertex `u` of the
4-element leftover `U` of a cover sees *all four* vertices of a packing block
`B`, the 8-vertex set `U ∪ B` splits into a triangle `T ⊆ U` and a new
quadrilateral `Q' ⊆ {u} ∪ B` plus one leftover vertex `x₀`.  Replacing `B` by
`Q'` in the packing therefore upgrades the cover `(S, U)` to a *covering
chain* `(T, S', x₀)`.

* `IsCover.chain_of_C3C4` — a `C₃ + C₄` decomposition of `U ∪ B` produces a
  chain whose packing is `insert Q' (S.erase B)`.
* `exists_C3C4_of_full_seer` — a vertex `u ∈ U` adjacent to every vertex of
  the block `B`, together with a triangle `T ⊆ U ∌ u`, supplies the
  `C₃ + C₄` decomposition.
* `IsCover.exists_chain_of_C3C4` — packaged form: from a `C₃ + C₄`
  decomposition occupying all but one vertex of `U ∪ B`, extract the leftover
  vertex `x₀` and build the chain.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- A cover `(S, U)` whose leftover together with a block `B ∈ S` splits as
`T ⊔ Q' ⊔ {x₀}` — a triangle, a quadrilateral block, and a single vertex —
produces the chain `(T, insert Q' (S.erase B), x₀)`. -/
theorem IsCover.chain_of_C3C4 {S : Finset (Finset V)} {U B T Q' : Finset V}
    {x0 : V} (hc : G.IsCover S U) (hB : B ∈ S)
    (hsub : T ∪ Q' ⊆ U ∪ B) (hTQ : Disjoint T Q')
    (hT : G.IsTriangle T) (hQ : G.IsQuadBlock Q')
    (hx0mem : x0 ∈ U ∪ B) (hx0nin : x0 ∉ T ∪ Q')
    (hcover : T ∪ Q' ∪ {x0} = U ∪ B) :
    G.IsChain T (insert Q' (S.erase B)) x0 := by
  have hBS : B ⊆ S.biUnion id := Finset.subset_biUnion_of_mem id hB
  -- The union of `S` splits off the block `B`.
  have hsplit : S.biUnion id = B ∪ (S.erase B).biUnion id := by
    conv_lhs => rw [← Finset.insert_erase hB]
    rw [Finset.biUnion_insert]
    rfl
  -- Every remaining block `C ∈ S.erase B` avoids all of `U ∪ B`.
  have hCdisj : ∀ C ∈ S.erase B, Disjoint C (U ∪ B) := by
    intro C hC
    obtain ⟨hCB, hCS⟩ := Finset.mem_erase.1 hC
    refine Finset.disjoint_union_right.2 ⟨?_, ?_⟩
    · exact hc.hdisj.mono_left (Finset.subset_biUnion_of_mem id hCS)
    · exact (hc.hS.2 B hB C hCS hCB.symm).symm
  have hQ'sub : Q' ⊆ U ∪ B := fun x hx => hsub (Finset.mem_union_right T hx)
  have hTsub : T ⊆ U ∪ B := fun x hx => hsub (Finset.mem_union_left _ hx)
  -- The remaining blocks together with `U ∪ B` still cover `V`.
  have hcovUB : (S.erase B).biUnion id ∪ (U ∪ B) = Finset.univ := by
    have hc2 := hc.hcover
    rw [hsplit] at hc2
    rw [← hc2]
    ext v
    simp only [Finset.mem_union]
    tauto
  refine ⟨hT, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- Every member of `insert Q' (S.erase B)` is a quadrilateral block.
    intro C hC
    rcases Finset.mem_insert.1 hC with rfl | hC
    · exact hQ
    · exact hc.hS.1 C (Finset.mem_erase.1 hC).2
  · -- The new packing is pairwise disjoint.
    intro C₁ h₁ C₂ h₂ hne
    rcases Finset.mem_insert.1 h₁ with hC₁ | h₁
    · rcases Finset.mem_insert.1 h₂ with hC₂ | h₂
      · exact absurd (hC₁.trans hC₂.symm) hne
      · rw [hC₁]
        exact Finset.disjoint_of_subset_left hQ'sub (hCdisj C₂ h₂).symm
    · rcases Finset.mem_insert.1 h₂ with hC₂ | h₂
      · rw [hC₂]
        exact Finset.disjoint_of_subset_right hQ'sub (hCdisj C₁ h₁)
      · exact hc.hS.2 C₁ (Finset.mem_erase.1 h₁).2 C₂
          (Finset.mem_erase.1 h₂).2 hne
  · -- `T` is disjoint from the new packing's union.
    rw [Finset.disjoint_left]
    intro x hxT hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    rcases Finset.mem_insert.1 hC with hCQ | hC
    · rw [hCQ] at hxC
      exact Finset.disjoint_left.1 hTQ hxT hxC
    · exact Finset.disjoint_left.1 (hCdisj C hC) hxC (hTsub hxT)
  · -- `x₀` is outside `T` and the new packing's union.
    intro h
    rcases Finset.mem_union.1 h with hxT | hx
    · exact hx0nin (Finset.mem_union_left _ hxT)
    · rw [Finset.mem_biUnion] at hx
      obtain ⟨C, hC, hxC⟩ := hx
      rcases Finset.mem_insert.1 hC with hCQ | hC
      · rw [hCQ] at hxC
        exact hx0nin (Finset.mem_union_right _ hxC)
      · exact Finset.disjoint_left.1 (hCdisj C hC) hxC hx0mem
  · -- Coverage: `T ∪ Q' ∪ {x₀} = U ∪ B` plus the remaining blocks.
    rw [Finset.biUnion_insert]
    have hrearr : T ∪ (id Q' ∪ (S.erase B).biUnion id) ∪ {x0}
        = (T ∪ Q' ∪ {x0}) ∪ (S.erase B).biUnion id := by
      ext v
      simp only [Finset.mem_union, Finset.mem_singleton, id_eq]
      tauto
    rw [hrearr, hcover,
      Finset.union_comm (U ∪ B) ((S.erase B).biUnion id)]
    exact hcovUB

omit [DecidableRel G.Adj] in
/-- If `u ∈ U` is adjacent to every vertex of a quadrilateral block `B`
disjoint from `U`, and `T ⊆ U` is a triangle avoiding `u`, then `U ∪ B`
contains a `C₃ + C₄` pair: the triangle `T` and the block `{u, a, x, b}`,
where `a - x - b` is a three-edge path inside `B`. -/
theorem exists_C3C4_of_full_seer {U B T : Finset V} {u : V}
    (hUB : Disjoint U B) (hB : G.IsQuadBlock B) (hu : u ∈ U)
    (hadj : ∀ x ∈ B, G.Adj u x)
    (hTsub : T ⊆ U) (hT : G.IsTriangle T) (huT : u ∉ T) :
    ∃ T' Q' : Finset V, T' ∪ Q' ⊆ U ∪ B ∧ Disjoint T' Q' ∧
      G.IsTriangle T' ∧ G.IsQuadBlock Q' := by
  obtain ⟨a, b, x, y, hB4, hab, hxy, e_ax, e_xb, e_by, e_ya⟩ := hB.exists_cycle
  have huB : u ∉ B := fun h => Finset.disjoint_left.1 hUB hu h
  have haB : a ∈ B := by simp [hB4]
  have hxB : x ∈ B := by simp [hB4]
  have hbB : b ∈ B := by simp [hB4]
  refine ⟨T, {u, a, x, b}, ?_, ?_, hT, ?_⟩
  · -- `T ∪ {u, a, x, b} ⊆ U ∪ B`.
    intro w hw
    rcases Finset.mem_union.1 hw with hwT | hwQ
    · exact Finset.mem_union_left _ (hTsub hwT)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hwQ
      rcases hwQ with rfl | rfl | rfl | rfl
      · exact Finset.mem_union_left _ hu
      · exact Finset.mem_union_right _ haB
      · exact Finset.mem_union_right _ hxB
      · exact Finset.mem_union_right _ hbB
  · -- `T` is disjoint from `{u, a, x, b}`: `u ∉ T` and `T ⊆ U`, `U ∩ B = ∅`.
    rw [Finset.disjoint_left]
    intro w hwT hwQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwQ
    rcases hwQ with rfl | rfl | rfl | rfl
    · exact huT hwT
    · exact Finset.disjoint_left.1 hUB (hTsub hwT) haB
    · exact Finset.disjoint_left.1 hUB (hTsub hwT) hxB
    · exact Finset.disjoint_left.1 hUB (hTsub hwT) hbB
  · -- The cycle `u - a - x - b - u` inside `{u, a, x, b}`.
    refine IsQuadBlock.of_cycle rfl
      (fun h => huB (h.symm ▸ haB)) (fun h => huB (h.symm ▸ hxB))
      (fun h => huB (h.symm ▸ hbB)) e_ax.ne hab e_xb.ne
      (hadj a haB) e_ax e_xb (hadj b hbB).symm

omit [DecidableRel G.Adj] in
/-- A cover `(S, U)` with a block `B ∈ S` such that `U ∪ B` minus one vertex
carries a `C₃ + C₄` decomposition produces a covering chain. -/
theorem IsCover.exists_chain_of_C3C4 {S : Finset (Finset V)} {U B : Finset V}
    (hc : G.IsCover S U) (hB : B ∈ S)
    (h : ∃ T' Q' : Finset V, T' ∪ Q' ⊆ U ∪ B ∧ Disjoint T' Q' ∧
      G.IsTriangle T' ∧ G.IsQuadBlock Q' ∧ (T' ∪ Q').card = 7) :
    ∃ (T : Finset V) (S' : Finset (Finset V)) (x0 : V),
      G.IsChain T S' x0 := by
  obtain ⟨T', Q', hsub, hTQ, hT', hQ', hcard7⟩ := h
  have hUB : Disjoint U B :=
    (hc.hdisj.mono_left (Finset.subset_biUnion_of_mem id hB)).symm
  have hcard8 : (U ∪ B).card = 8 := by
    rw [Finset.card_union_of_disjoint hUB, hc.hcard, (hc.hS.1 B hB).1]
  -- The leftover `(U ∪ B) \ (T' ∪ Q')` is a single vertex `x₀`.
  have hleft : ((U ∪ B) \ (T' ∪ Q')).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hcard8, hcard7]
  obtain ⟨x0, hx0⟩ := Finset.card_eq_one.1 hleft
  have hx0L : x0 ∈ (U ∪ B) \ (T' ∪ Q') := by
    rw [hx0]
    exact Finset.mem_singleton_self x0
  have hx0mem : x0 ∈ U ∪ B := (Finset.mem_sdiff.1 hx0L).1
  have hx0nin : x0 ∉ T' ∪ Q' := (Finset.mem_sdiff.1 hx0L).2
  have hcover : T' ∪ Q' ∪ {x0} = U ∪ B := by
    rw [← hx0]
    exact Finset.union_sdiff_of_subset hsub
  exact ⟨T', insert Q' (S.erase B), x0,
    hc.chain_of_C3C4 hB hsub hTQ hT' hQ' hx0mem hx0nin hcover⟩

end SimpleGraph
