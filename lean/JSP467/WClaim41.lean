import JSP467.WChain
import JSP467.Chord
import JSP467.Heavy
import JSP467.Pairing
import JSP467.WCount

/-!
# JSP-000467 — Wang's Claim 4.1(a): terminal swaps in a feasible chain

Wang's Lemma 4.1(a) says that for a feasible chain `(T, S, x₀)` the terminal
vertex `x₀` can replace any freeable `w` of a quadrilateral block `B ∈ S`
— the swapped family is again a chain — and that `blockSum`-maximality
transfers the local degree comparison from the packing setting
(`blockSum_exchange_le`, `freeable_universal_of_full`) to the chain setting:

* `IsChain.terminal_swap` — the swap `x₀ ↔ w` produces a chain with new
  terminal `w`.
* `feasible_terminal_exchange_le` — `x₀` sees at most as many of
  `B.erase w` as `w` does.
* `feasible_terminal_freeable_universal` — if `x₀` sees all three remaining
  vertices of `B.erase w`, then a freeable `w` is universal inside `B`
  (the chain analogue of `freeable_universal_of_three`).
* `feasible_terminal_full_seer_k4` — if `x₀` is adjacent to all four
  vertices of `B`, then `B` spans `K₄` (`edgeSum G B = 12`).
* `feasible_terminal_three_seer_missed` — if `x₀` sees exactly three
  vertices of `B`, missing `b0`, and `b0` is freeable, then `b0` is
  universal inside `B`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- **Terminal swap.**  If `(T, S, x₀)` is a chain and `w ∈ B ∈ S` is
freeable for the terminal `x₀` (i.e. `insert x₀ (B.erase w)` is again a
quadrilateral block), then replacing `B` by the swapped block and moving
the terminal to `w` is again a chain. -/
theorem IsChain.terminal_swap {T : Finset V} {S : Finset (Finset V)}
    {x0 w : V} {B : Finset V}
    (hc : G.IsChain T S x0) (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert x0 (B.erase w))) :
    G.IsChain T (insert (insert x0 (B.erase w)) (S.erase B)) w := by
  have hx0U : x0 ∉ S.biUnion id :=
    fun h => hc.hx0 (Finset.mem_union_right T h)
  obtain ⟨hS', -, hU'⟩ := hc.hS.exchange_block hx0U hB hw hBw
  have hwU : w ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB hw
  have hwT : w ∉ T := fun h =>
    Finset.disjoint_left.1 hc.hTS h hwU
  have hwx0 : w ≠ x0 := fun h => hx0U (h ▸ hwU)
  refine ⟨hc.hT, hS', ?_, ?_, ?_⟩
  · -- The new covered set `(∪S).erase w ∪ {x0}` is still disjoint from `T`.
    rw [hU', Finset.disjoint_union_right]
    exact ⟨hc.hTS.mono_right (Finset.erase_subset _ _),
      Finset.disjoint_singleton_right.2
        (fun h => hc.hx0 (Finset.mem_union_left _ h))⟩
  · -- The new terminal `w` is outside `T` and outside the new covered set.
    intro h
    rcases Finset.mem_union.1 h with hT' | hS''
    · exact hwT hT'
    · rw [hU'] at hS''
      rcases Finset.mem_union.1 hS'' with h1 | h2
      · exact (Finset.mem_erase.1 h1).1 rfl
      · exact hwx0 (Finset.mem_singleton.1 h2)
  · -- Coverage: the old chain covered `V`, and `w` stays covered via `{w}`.
    apply Finset.eq_univ_of_forall
    intro v
    have hv : v ∈ T ∪ S.biUnion id ∪ {x0} := by
      rw [hc.hcov]; exact Finset.mem_univ v
    rw [hU']
    rcases Finset.mem_union.1 hv with hv' | hvx
    · rcases Finset.mem_union.1 hv' with hvT | hvU
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hvT)
      · by_cases hvw : v = w
        · subst hvw
          exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hvw, hvU⟩)))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_union_right _ hvx))

/-- **Chain exchange inequality.**  In a feasible chain, a freeable
`w ∈ B` sees at least as many of the remaining block vertices `B.erase w`
as the terminal `x₀` does: the swap produces a chain, so `blockSum` cannot
increase. -/
theorem feasible_terminal_exchange_le {T : Finset V} {S : Finset (Finset V)}
    {x0 w : V} {B : Finset V}
    (hc : G.IsFeasibleChain T S x0) (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert x0 (B.erase w))) :
    ((B.erase w) ∩ G.neighborFinset x0).card ≤
      ((B.erase w) ∩ G.neighborFinset w).card := by
  have hx0U : x0 ∉ S.biUnion id :=
    fun h => hc.1.hx0 (Finset.mem_union_right T h)
  have hx0B : x0 ∉ B := fun h =>
    hx0U (Finset.subset_biUnion_of_mem id hB h)
  have hchain := hc.1.terminal_swap hB hw hBw
  have hle := hc.2.1 T _ w hchain
  -- The new block is genuinely new: it contains `x0`, which no old block
  -- does (`x0 ∉ ⋃ S`).
  have hB'nin : insert x0 (B.erase w) ∉ S.erase B := by
    intro h
    exact hx0U (Finset.subset_biUnion_of_mem id (Finset.mem_erase.1 h).2
      (Finset.mem_insert_self x0 _))
  have hsum1 : blockSum G (insert (insert x0 (B.erase w)) (S.erase B))
      = edgeSum G (insert x0 (B.erase w)) + blockSum G (S.erase B) := by
    simp only [blockSum]
    exact Finset.sum_insert hB'nin
  have hsum2 : blockSum G S
      = edgeSum G B + blockSum G (S.erase B) := by
    simp only [blockSum]
    conv_lhs => rw [← Finset.insert_erase hB]
    rw [Finset.sum_insert (Finset.notMem_erase B S)]
  rw [hsum1, hsum2] at hle
  have hex := edgeSum_block_exchange (G := G) B hx0B hw
  omega

/-- **Chain analogue of `freeable_universal_of_three`.**  In a feasible
chain, if the terminal `x₀` sees all three vertices of `B.erase w` for a
freeable `w ∈ B`, then `w` is universal inside `B` (adjacent to the other
three block vertices). -/
theorem feasible_terminal_freeable_universal {T : Finset V}
    {S : Finset (Finset V)} {x0 w : V} {B : Finset V}
    (hc : G.IsFeasibleChain T S x0) (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert x0 (B.erase w)))
    (h3 : (B.erase w ∩ G.neighborFinset x0).card = 3) :
    ∀ x ∈ B, x ≠ w → G.Adj w x := by
  have hle := feasible_terminal_exchange_le hc hB hw hBw
  have hBcard : B.card = 4 := (hc.1.hS.1 B hB).1
  have herase : (B.erase w).card = 3 := by
    rw [Finset.card_erase_of_mem hw, hBcard]
  rw [h3] at hle
  -- `(B.erase w) ∩ N w` is a 3-element subset of the 3-element `B.erase w`.
  have heq : B.erase w ∩ G.neighborFinset w = B.erase w :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [herase]; exact hle)
  intro x hx hxw
  have hxn : x ∈ B.erase w ∩ G.neighborFinset w := by
    rw [heq]
    exact Finset.mem_erase.2 ⟨hxw, hx⟩
  exact (G.mem_neighborFinset w x).1 (Finset.mem_inter.1 hxn).2

/-- **Full seer ⇒ `K₄` (chain version).**  In a feasible chain, if the
terminal `x₀` is adjacent to all four vertices of the block `B`, then every
`w ∈ B` is universal inside `B`, so `B` spans `K₄`:
`edgeSum G B = 12`. -/
theorem feasible_terminal_full_seer_k4 {T : Finset V} {S : Finset (Finset V)}
    {x0 : V} {B : Finset V}
    (hc : G.IsFeasibleChain T S x0) (hB : B ∈ S)
    (h4 : (B ∩ G.neighborFinset x0).card = 4) :
    edgeSum G B = 12 := by
  have hBq : G.IsQuadBlock B := hc.1.hS.1 B hB
  have hBcard : B.card = 4 := hBq.1
  have hx0U : x0 ∉ S.biUnion id :=
    fun h => hc.1.hx0 (Finset.mem_union_right T h)
  have hx0B : x0 ∉ B := fun h =>
    hx0U (Finset.subset_biUnion_of_mem id hB h)
  have hadj : ∀ x ∈ B, G.Adj x0 x :=
    card_four_subset_neighbor_of_full hBcard h4
  -- Every `w ∈ B` is freeable (`x₀` sees all of `B`), hence universal in `B`.
  have huniv : ∀ w ∈ B, ∀ x ∈ B, x ≠ w → G.Adj w x := by
    intro w hw
    apply feasible_terminal_freeable_universal hc hB hw
      (IsQuadBlock.exchange_all hBq hx0B hadj w hw)
    have hsub : B.erase w ⊆ G.neighborFinset x0 := fun x hx =>
      (G.mem_neighborFinset x0 x).2 (hadj x (Finset.mem_of_mem_erase hx))
    rw [Finset.inter_eq_left.2 hsub, Finset.card_erase_of_mem hw, hBcard]
  -- Each vertex of `B` has exactly the other three vertices as neighbours
  -- inside `B`.
  have hterm : ∀ w ∈ B, (B ∩ G.neighborFinset w).card = 3 := by
    intro w hw
    have hset : B ∩ G.neighborFinset w = B.erase w := by
      ext x
      simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_erase]
      constructor
      · rintro ⟨hxB, hxa⟩
        exact ⟨(G.ne_of_adj hxa).symm, hxB⟩
      · rintro ⟨hxw, hxB⟩
        exact ⟨hxB, huniv w hw x hxB hxw⟩
    rw [hset, Finset.card_erase_of_mem hw, hBcard]
  calc edgeSum G B = ∑ _w ∈ B, 3 := Finset.sum_congr rfl hterm
    _ = 12 := by rw [Finset.sum_const, smul_eq_mul, hBcard]

/-- **Three-seer restriction at the missed vertex (chain version).**  In a
feasible chain, if the terminal `x₀` sees exactly three of the four vertices
of `B`, missing `b0`, and the missed vertex `b0` itself is freeable, then
`b0` is universal inside `B`. -/
theorem feasible_terminal_three_seer_missed {T : Finset V}
    {S : Finset (Finset V)} {x0 b0 : V} {B : Finset V}
    (hc : G.IsFeasibleChain T S x0) (hB : B ∈ S) (hb0 : b0 ∈ B)
    (hnadj : ¬ G.Adj x0 b0)
    (h3 : (B ∩ G.neighborFinset x0).card = 3)
    (hB0 : G.IsQuadBlock (insert x0 (B.erase b0))) :
    ∀ x ∈ B, x ≠ b0 → G.Adj b0 x := by
  -- `x₀`'s neighbours inside `B` all differ from `b0`.
  have hcap : B.erase b0 ∩ G.neighborFinset x0
      = B ∩ G.neighborFinset x0 := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase, G.mem_neighborFinset]
    constructor
    · rintro ⟨⟨-, hxB⟩, hxu⟩
      exact ⟨hxB, hxu⟩
    · rintro ⟨hxB, hxu⟩
      exact ⟨⟨fun h => hnadj (h ▸ hxu), hxB⟩, hxu⟩
  exact feasible_terminal_freeable_universal hc hB hb0 hB0
    (by rw [hcap, h3])

end SimpleGraph
