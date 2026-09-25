import JSP467.Cascade

/-!
# JSP-000467 — the "rotate-back / hole-relocation" machinery

Wang's switching argument (Wa10): when the uncovered vertex `u` is exchanged
into a packing block `B` freeing `w`, it may happen that `w` is itself heavy
on the *new* block `B' = insert u (B.erase w)` (at least three neighbours
inside it).  Then `w` can be exchanged back into `B'`, and since
`exists_two_freeable` provides *two* freeable vertices of `B'` for `w`, one
of them differs from `u`: the freed vertex `w₂` lies in `B.erase w`.  The
net effect is a packing of the same cardinality whose covered set is
`(∪S).erase w₂ ∪ {u}` — the "hole" moved from `u` to a different vertex `w₂`
inside the same block region while `u` was absorbed.

## Main results

* `exists_hole_move_same_block` — the hole relocation on the covered set.
* `exists_hole_move_same_block_leftover` — the same statement phrased on the
  leftover set: `univ \ ∪S₂ = (univ \ ∪S).erase u ∪ {w₂}`.
* `exists_larger_of_hole_move_same_block` — after the hole move, a
  quadrilateral block inside the new leftover yields a larger packing.
* `freed_heavy_back_of_adj` — the rotate-back heaviness test: if `w` is
  adjacent to `u` and has two neighbours among the remaining block vertices,
  `w` is heavy on the exchanged block.
* `freed_two_nbrs_of_lexmax` — `blockSum`-maximality (a consequence of the
  lexicographic maximality `hlex`) forces any freeable `w` to keep at least
  two neighbours inside `B.erase w` (`blockSum_exchange_le`).
* `freed_heavy_back_of_lexmax` — at a lex-max packing *every* freeable `w`
  is heavy back on `B'`: if `w ~ u`, two neighbours plus `u` itself; if
  `w ≁ u`, all three of `u`'s neighbours in `B` avoid `w` and transfer.
* `exists_rotate_back` — the assembled rotate-back step under `hnolarger`:
  the relocated packing `S₂`, the new hole `w₂`, the conditional
  heaviness of `w₂`, and the next low-degree heavy vertex `u₂`.
* `exists_larger_of_rotate_back` — the enlargement reduced to the relocated
  configuration (a hypothesis-parameter `hclose` receives the full rotated
  state).
* `exists_larger_of_rotate_back_of_leftover` — unconditional enlargement
  when the relocated leftover contains a quadrilateral block.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **Hole relocation inside one block.**  If the uncovered vertex `u` can
replace `w₁` in the packing block `B₁` (the swapped set `B₁'` remaining a
quadrilateral block) and `w₁` still sees at least three vertices of `B₁'`,
then `w₁` can be exchanged back into `B₁'` at a vertex `w₂ ≠ u` — hence
`w₂ ∈ B₁.erase w₁` — producing a packing of the same cardinality covering
`(∪S).erase w₂ ∪ {u}`: `w₁` is reabsorbed and the hole lands on `w₂`. -/
theorem exists_hole_move_same_block [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    {u w₁ : V} {B₁ : Finset V}
    (hu : u ∉ S.biUnion id) (hB₁ : B₁ ∈ S) (hw₁ : w₁ ∈ B₁)
    (hBw₁ : G.IsQuadBlock (insert u (B₁.erase w₁)))
    (hheavy₁ : 3 ≤ ((insert u (B₁.erase w₁)) ∩ G.neighborFinset w₁).card) :
    ∃ w₂ ∈ B₁.erase w₁, ∃ S₂ : Finset (Finset V),
      G.IsQuadPacking S₂ ∧ S₂.card = S.card ∧
      S₂.biUnion id = (S.biUnion id).erase w₂ ∪ {u} := by
  -- Book-keeping: `w₁` is covered by `S` and differs from `u`.
  have hw₁X : w₁ ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB₁ hw₁
  have hw₁u : w₁ ≠ u := fun h => hu (h ▸ hw₁X)
  -- First exchange: `u` replaces `w₁` in `B₁`, giving the packing `S₁`.
  obtain ⟨hP₁, hC₁, hU₁⟩ := hS.exchange_block hu hB₁ hw₁ hBw₁
  -- `w₁` is uncovered by `S₁`: it is missing from `(∪S).erase w₁` and
  -- `w₁ ≠ u`.
  have hw₁nin : w₁ ∉
      (insert (insert u (B₁.erase w₁)) (S.erase B₁)).biUnion id := by
    rw [hU₁, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    rintro (⟨h, -⟩ | h)
    · exact h rfl
    · exact hw₁u h
  -- `B₁'` is a block of `S₁`.
  have hB₁'in : insert u (B₁.erase w₁) ∈
      insert (insert u (B₁.erase w₁)) (S.erase B₁) :=
    Finset.mem_insert_self _ _
  -- `w₁ ∉ B₁'`: it is neither `u` nor in `B₁.erase w₁`.
  have hw₁nB' : w₁ ∉ insert u (B₁.erase w₁) := by
    rw [Finset.mem_insert, Finset.mem_erase]
    rintro (h | ⟨h, -⟩)
    · exact hw₁u h
    · exact h rfl
  -- Two vertices of `B₁'` are freeable for `w₁`; at least one differs
  -- from `u`.
  obtain ⟨a, b, haB', hbB', hab, haQ, hbQ⟩ :=
    exists_two_freeable hBw₁ hw₁nB' hheavy₁
  obtain ⟨w₂, hw₂B', hw₂u, hw₂Q⟩ : ∃ w₂ ∈ insert u (B₁.erase w₁), w₂ ≠ u ∧
      G.IsQuadBlock (insert w₁ ((insert u (B₁.erase w₁)).erase w₂)) := by
    by_cases hau : a = u
    · exact ⟨b, hbB', fun h => hab (hau.trans h.symm), hbQ⟩
    · exact ⟨a, haB', hau, haQ⟩
  -- Since `w₂ ≠ u`, it lies in `B₁.erase w₁`; in particular `w₂ ≠ w₁` and
  -- `w₂` is covered by `S`.
  have hw₂B : w₂ ∈ B₁.erase w₁ := by
    rcases Finset.mem_insert.1 hw₂B' with h | h
    · exact absurd h hw₂u
    · exact h
  have hw₂w₁ : w₂ ≠ w₁ := (Finset.mem_erase.1 hw₂B).1
  have hw₁w₂ : w₁ ≠ w₂ := hw₂w₁.symm
  -- Second exchange: `w₁` replaces `w₂` in `B₁'`, giving the packing `S₂`.
  obtain ⟨hP₂, hC₂, hU₂⟩ := hP₁.exchange_block hw₁nin hB₁'in hw₂B' hw₂Q
  refine ⟨w₂, hw₂B, _, hP₂, hC₂.trans hC₁, ?_⟩
  rw [hU₂, hU₁]
  -- Set algebra: `((X.erase w₁ ∪ {u}).erase w₂) ∪ {w₁} = X.erase w₂ ∪ {u}`.
  ext x
  by_cases hx₁ : x = w₁
  · subst hx₁
    simp [hw₁w₂, hw₁X]
  · by_cases hx₂ : x = w₂
    · subst hx₂
      simp [hx₁, hw₂u]
    · by_cases hxu : x = u
      · subst hxu
        simp [hx₁, hx₂]
      · simp [hx₁, hx₂, hxu]

/-- **Hole relocation, leftover form.**  Under the hypotheses of
`exists_hole_move_same_block`, the leftover of the twice-exchanged packing
is `(univ \ ∪S).erase u ∪ {w₂}`: `u` is absorbed and `w₂` is freed. -/
theorem exists_hole_move_same_block_leftover [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    {u w₁ : V} {B₁ : Finset V}
    (hu : u ∉ S.biUnion id) (hB₁ : B₁ ∈ S) (hw₁ : w₁ ∈ B₁)
    (hBw₁ : G.IsQuadBlock (insert u (B₁.erase w₁)))
    (hheavy₁ : 3 ≤ ((insert u (B₁.erase w₁)) ∩ G.neighborFinset w₁).card) :
    ∃ w₂ ∈ B₁.erase w₁, ∃ S₂ : Finset (Finset V),
      G.IsQuadPacking S₂ ∧ S₂.card = S.card ∧
      Finset.univ \ S₂.biUnion id =
        (Finset.univ \ S.biUnion id).erase u ∪ {w₂} := by
  obtain ⟨w₂, hw₂, S₂, hP₂, hC₂, hU₂⟩ :=
    exists_hole_move_same_block hS hu hB₁ hw₁ hBw₁ hheavy₁
  have hw₂X : w₂ ∈ S.biUnion id :=
    Finset.subset_biUnion_of_mem id hB₁ (Finset.mem_erase.1 hw₂).2
  have hw₂u : w₂ ≠ u := fun h => hu (h ▸ hw₂X)
  refine ⟨w₂, hw₂, S₂, hP₂, hC₂, ?_⟩
  rw [hU₂]
  -- Set algebra: `univ \ (X.erase w₂ ∪ {u}) = (univ \ X).erase u ∪ {w₂}`.
  ext x
  by_cases hx₂ : x = w₂
  · subst hx₂
    simp [hw₂u]
  · by_cases hxu : x = u
    · subst hxu
      simp [hx₂]
    · simp [hx₂, hxu]

/-- **Enlargement after a hole move.**  If the hole can be relocated to
`w₂ ∈ B₁.erase w₁` and, for the freed `w₂`, a quadrilateral block `Q` sits
inside the new leftover `(univ \ ∪S).erase u ∪ {w₂}`, then a strictly larger
packing exists. -/
theorem exists_larger_of_hole_move_same_block [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    {u w₁ : V} {B₁ : Finset V}
    (hu : u ∉ S.biUnion id) (hB₁ : B₁ ∈ S) (hw₁ : w₁ ∈ B₁)
    (hBw₁ : G.IsQuadBlock (insert u (B₁.erase w₁)))
    (hheavy₁ : 3 ≤ ((insert u (B₁.erase w₁)) ∩ G.neighborFinset w₁).card)
    (hQ : ∀ w₂ ∈ B₁.erase w₁, ∃ Q : Finset V,
      G.IsQuadBlock Q ∧
      Q ⊆ (Finset.univ \ S.biUnion id).erase u ∪ {w₂}) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  obtain ⟨w₂, hw₂, S₂, hP₂, hC₂, hU₂⟩ :=
    exists_hole_move_same_block_leftover hS hu hB₁ hw₁ hBw₁ hheavy₁
  obtain ⟨Q, hQB, hQsub⟩ := hQ w₂ hw₂
  have hQsub' : Q ⊆ Finset.univ \ S₂.biUnion id := by
    rw [hU₂]
    exact hQsub
  obtain ⟨T, hT, hcard⟩ := exists_larger_of_leftover_block hP₂ hQB hQsub'
  exact ⟨T, hT, by omega⟩

/-- **Rotate-back heaviness test.**  If `w ∈ B` is adjacent to `u` and has
at least two neighbours among the remaining block vertices `B.erase w`,
then `w` is heavy on the exchanged block `B' = insert u (B.erase w)`: it
sees `u` together with its two neighbours in `B.erase w`. -/
theorem freed_heavy_back_of_adj [DecidableRel G.Adj] {B : Finset V}
    {u w : V} (hw : w ∈ B) (huB : u ∉ B) (hadj : G.Adj w u)
    (h2 : 2 ≤ ((B.erase w) ∩ G.neighborFinset w).card) :
    3 ≤ ((insert u (B.erase w)) ∩ G.neighborFinset w).card := by
  -- `u` contributes a fresh neighbour: `u ∉ B.erase w`.
  have hun : u ∉ (B.erase w) ∩ G.neighborFinset w :=
    fun h => huB (Finset.mem_of_mem_erase (Finset.mem_inter.1 h).1)
  -- `{u} ∪ ((B.erase w) ∩ N w)` is a `1 + (≥2)`-element subset of
  -- `B' ∩ N w`.
  have hsub : insert u ((B.erase w) ∩ G.neighborFinset w)
      ⊆ (insert u (B.erase w)) ∩ G.neighborFinset w := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact Finset.mem_inter.2 ⟨Finset.mem_insert_self _ _,
        (G.mem_neighborFinset w x).2 hadj⟩
    · obtain ⟨hxB, hxw⟩ := Finset.mem_inter.1 hx
      exact Finset.mem_inter.2 ⟨Finset.mem_insert_of_mem hxB, hxw⟩
  have hcard : (insert u ((B.erase w) ∩ G.neighborFinset w)).card
      = ((B.erase w) ∩ G.neighborFinset w).card + 1 :=
    Finset.card_insert_of_notMem hun
  have h3 : 3 ≤ (insert u ((B.erase w) ∩ G.neighborFinset w)).card := by
    rw [hcard]
    omega
  exact h3.trans (Finset.card_le_card hsub)

/-- **Two remaining neighbours for the freed vertex.**  At a
`blockSum`-maximal packing (in particular at the lexicographic maximizer
`hlex`), a freeable `w ∈ B` keeps at least two neighbours inside
`B.erase w`: `blockSum_exchange_le` transfers `u`'s neighbour count, and at
most one of `u`'s `≥ 3` neighbours in `B` can be `w` itself. -/
theorem freed_two_nbrs_of_lexmax [DecidableRel G.Adj] {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    {u w : V} {B : Finset V}
    (hu : u ∉ S.biUnion id) (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert u (B.erase w)))
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    2 ≤ ((B.erase w) ∩ G.neighborFinset w).card := by
  -- The lexicographic bound gives plain `blockSum`-maximality.
  have hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T →
      T.card = S.card → blockSum G T ≤ blockSum G S :=
    fun T hT hTm => (hlex T hT hTm).elim le_of_lt fun h => le_of_eq h.1
  have hle := blockSum_exchange_le hS hmax hu hB hw hBw
  -- `B ∩ N u ⊆ {w} ∪ ((B.erase w) ∩ N u)`, so `|(B.erase w) ∩ N u| ≥ 2`.
  have hsub : B ∩ G.neighborFinset u
      ⊆ insert w ((B.erase w) ∩ G.neighborFinset u) := by
    intro x hx
    obtain ⟨hxB, hxu⟩ := Finset.mem_inter.1 hx
    by_cases hxw : x = w
    · rw [hxw]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_inter.2
        ⟨Finset.mem_erase.2 ⟨hxw, hxB⟩, hxu⟩)
  have hcardle := Finset.card_le_card hsub
  have hins :=
    Finset.card_insert_le w ((B.erase w) ∩ G.neighborFinset u)
  omega

/-- **The freed vertex is always heavy back at a lex-max packing.**  Any
freeable `w ∈ B` (with `u` heavy on `B`) has `≥ 3` neighbours inside the
exchanged block `B' = insert u (B.erase w)`: if `w ~ u`, two of them lie in
`B.erase w` (`freed_two_nbrs_of_lexmax`) and `u` is the third; if `w ≁ u`,
all `≥ 3` neighbours of `u` in `B` already avoid `w`, so
`blockSum_exchange_le` transfers at least three neighbours of `w` inside
`B.erase w ⊆ B'`. -/
theorem freed_heavy_back_of_lexmax [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    {u w : V} {B : Finset V}
    (hu : u ∉ S.biUnion id) (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert u (B.erase w)))
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    3 ≤ ((insert u (B.erase w)) ∩ G.neighborFinset w).card := by
  have huB : u ∉ B := fun h => hu (Finset.subset_biUnion_of_mem id hB h)
  by_cases hadj : G.Adj w u
  · exact freed_heavy_back_of_adj hw huB hadj
      (freed_two_nbrs_of_lexmax hS hlex hu hB hw hBw h3)
  · -- `w ≁ u`: every neighbour of `u` in `B` lies in `B.erase w`, and the
    -- count transfers to `w`.
    have hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T →
        T.card = S.card → blockSum G T ≤ blockSum G S :=
      fun T hT hTm => (hlex T hT hTm).elim le_of_lt fun h => le_of_eq h.1
    have hle := blockSum_exchange_le hS hmax hu hB hw hBw
    have hsub : B ∩ G.neighborFinset u
        ⊆ (B.erase w) ∩ G.neighborFinset u := by
      intro x hx
      obtain ⟨hxB, hxu⟩ := Finset.mem_inter.1 hx
      refine Finset.mem_inter.2 ⟨Finset.mem_erase.2 ⟨?_, hxB⟩, hxu⟩
      intro hxw
      exact hadj (hxw ▸ (G.mem_neighborFinset u x).1 hxu).symm
    have h3' : 3 ≤ ((B.erase w) ∩ G.neighborFinset u).card :=
      h3.trans (Finset.card_le_card hsub)
    have hfin : (B.erase w) ∩ G.neighborFinset w
        ⊆ (insert u (B.erase w)) ∩ G.neighborFinset w := by
      intro x hx
      obtain ⟨hxB, hxw⟩ := Finset.mem_inter.1 hx
      exact Finset.mem_inter.2 ⟨Finset.mem_insert_of_mem hxB, hxw⟩
    exact (h3'.trans hle).trans (Finset.card_le_card hfin)

/-- **Hole relocation at a lex-max packing.**  The heavy-back hypothesis of
`exists_hole_move_same_block` is automatic at the lexicographic maximizer:
any freeable `w₁` is heavy on the exchanged block. -/
theorem exists_hole_move_same_block_of_lexmax [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    {u w₁ : V} {B₁ : Finset V}
    (hu : u ∉ S.biUnion id) (hB₁ : B₁ ∈ S) (hw₁ : w₁ ∈ B₁)
    (hBw₁ : G.IsQuadBlock (insert u (B₁.erase w₁)))
    (h3 : 3 ≤ (B₁ ∩ G.neighborFinset u).card) :
    ∃ w₂ ∈ B₁.erase w₁, ∃ S₂ : Finset (Finset V),
      G.IsQuadPacking S₂ ∧ S₂.card = S.card ∧
      S₂.biUnion id = (S.biUnion id).erase w₂ ∪ {u} :=
  exists_hole_move_same_block hS hu hB₁ hw₁ hBw₁
    (freed_heavy_back_of_lexmax hS hlex hu hB₁ hw₁ hBw₁ h3)

/-- **Assembled rotate-back step.**  At a lex-max non-covering packing under
`hnolarger`, exchanging the heavy leftover vertex `u` for a freeable
`w ∈ B` and rotating `w` back produces a same-cardinality packing `S₂`
covering `(∪S).erase w₂ ∪ {u}` — the hole relocated to `w₂ ∈ B.erase w`.
The output packages the full next cascade state: the covering and leftover
equations, the `blockSum` bound, the conditional rotation bound and
heaviness of the new hole `w₂`, and (via `hnolarger` at `S₂`) the next
low-leftover-degree heavy vertex `u₂` with its heavy block `B₂ ∈ S₂`. -/
theorem exists_rotate_back (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) (hlt : S.card < k)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    (hnolarger : ¬ ∃ T : Finset (Finset V),
      G.IsQuadPacking T ∧ S.card < T.card)
    {u w : V} {B : Finset V}
    (hu : u ∈ Finset.univ \ S.biUnion id)
    (hudeg : ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card
      ≤ 2 * (k - S.card) - 1)
    (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert u (B.erase w)))
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    ∃ (w₂ : V) (S₂ : Finset (Finset V)) (u₂ : V) (B₂ : Finset V),
      w₂ ∈ B.erase w ∧ w₂ ∈ S.biUnion id ∧ w₂ ≠ u ∧
      G.IsQuadPacking S₂ ∧ S₂.card = S.card ∧
      S₂.biUnion id = (S.biUnion id).erase w₂ ∪ {u} ∧
      Finset.univ \ S₂.biUnion id
        = (Finset.univ \ S.biUnion id).erase u ∪ {w₂} ∧
      blockSum G S₂ ≤ blockSum G S ∧
      (blockSum G S₂ = blockSum G S →
        ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w₂).card
          ≤ 2 * (k - S.card) - 1) ∧
      (blockSum G S₂ = blockSum G S →
        ∃ B'' ∈ S₂, 3 ≤ (B'' ∩ G.neighborFinset w₂).card) ∧
      u₂ ∈ Finset.univ \ S₂.biUnion id ∧
      ((Finset.univ \ S₂.biUnion id) ∩ G.neighborFinset u₂).card
        ≤ 2 * (k - S.card) - 1 ∧
      B₂ ∈ S₂ ∧ 3 ≤ (B₂ ∩ G.neighborFinset u₂).card := by
  classical
  have hu' : u ∉ S.biUnion id := (Finset.mem_sdiff.1 hu).2
  -- The heavy-back condition is automatic at a lex-max packing.
  have hback := freed_heavy_back_of_lexmax hS hlex hu' hB hw hBw h3
  -- The hole move: `u` is absorbed, `w₂ ∈ B.erase w` becomes the hole.
  obtain ⟨w₂, hw₂B, S₂, hP₂, hC₂, hX₂⟩ :=
    exists_hole_move_same_block hS hu' hB hw hBw hback
  have hw₂X : w₂ ∈ S.biUnion id :=
    Finset.subset_biUnion_of_mem id hB (Finset.mem_of_mem_erase hw₂B)
  have hw₂u : w₂ ≠ u := fun h => hu' (h ▸ hw₂X)
  have hUb₂ : Finset.univ \ S₂.biUnion id
      = (Finset.univ \ S.biUnion id).erase u ∪ {w₂} := by
    rw [hX₂]
    exact univ_sdiff_erase_union_singleton hw₂X hu'
  -- `hnolarger` and the cardinality bound transfer to `S₂`.
  have hlt₂ : S₂.card < k := hC₂ ▸ hlt
  have hnolarger₂ := no_larger_of_card_eq hC₂ hnolarger
  -- `blockSum` cannot increase (the lex bound applied at `S₂`).
  have hbs : blockSum G S₂ ≤ blockSum G S := by
    rcases hlex S₂ hP₂ hC₂ with hlt' | ⟨heq, -⟩
    · exact le_of_lt hlt'
    · exact le_of_eq heq
  -- Conditional rotation bound for `w₂`: if `blockSum` is preserved, the
  -- lex bound forces `edgeSum` of the leftover down, which
  -- `edgeSum_exchange` unwraps to `w₂`'s leftover degree ≤ `u`'s.
  have hw₂nin : w₂ ∉ Finset.univ \ S.biUnion id :=
    fun h => (Finset.mem_sdiff.1 h).2 hw₂X
  have hrot : blockSum G S₂ = blockSum G S →
      ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w₂).card
        ≤ 2 * (k - S.card) - 1 := by
    intro heq
    have hle : edgeSum G (Finset.univ \ S₂.biUnion id)
        ≤ edgeSum G (Finset.univ \ S.biUnion id) := by
      rcases hlex S₂ hP₂ hC₂ with hlt' | ⟨-, hle⟩
      · rw [heq] at hlt'
        omega
      · exact hle
    rw [hUb₂, edgeSum_exchange _ hu hw₂nin] at hle
    omega
  -- When `blockSum` is preserved, the new hole `w₂` is itself heavy on
  -- some block of `S₂`.
  have hheavy₂ : blockSum G S₂ = blockSum G S →
      ∃ B'' ∈ S₂, 3 ≤ (B'' ∩ G.neighborFinset w₂).card :=
    fun heq => freed_w_heavy_of_rotBound G k hmin hP₂ hC₂ hlt hUb₂ (hrot heq)
  -- The dichotomy at `S₂` supplies the next heavy vertex `u₂`.
  obtain ⟨u₂, hu₂U, hdeg₂, B₂, hB₂S₂, h3₂⟩ :=
    exists_heavy_lowdeg_of_no_larger G k hcard hmin hP₂ hlt₂ hnolarger₂
  refine ⟨w₂, S₂, u₂, B₂, hw₂B, hw₂X, hw₂u, hP₂, hC₂, hX₂, hUb₂, hbs, hrot,
    hheavy₂, hu₂U, ?_, hB₂S₂, h3₂⟩
  rwa [hC₂] at hdeg₂

/-- **Enlargement reduced to the relocated-hole configuration.**  Under
`hnolarger`, the rotate-back step moves the hole from `u` to
`w₂ ∈ B.erase w` and produces the next heavy vertex `u₂`; to conclude an
enlargement it suffices to close the fully-packaged rotated state
(`hclose`).  The residual `hclose` is an explicit hypothesis parameter —
fully proved, no axiom. -/
theorem exists_larger_of_rotate_back (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) (hlt : S.card < k)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    (hnolarger : ¬ ∃ T : Finset (Finset V),
      G.IsQuadPacking T ∧ S.card < T.card)
    {u w : V} {B : Finset V}
    (hu : u ∈ Finset.univ \ S.biUnion id)
    (hudeg : ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card
      ≤ 2 * (k - S.card) - 1)
    (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert u (B.erase w)))
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card)
    (hclose : ∀ (w₂ : V) (S₂ : Finset (Finset V)) (u₂ : V) (B₂ : Finset V),
      w₂ ∈ B.erase w → w₂ ∈ S.biUnion id → w₂ ≠ u →
      G.IsQuadPacking S₂ → S₂.card = S.card →
      S₂.biUnion id = (S.biUnion id).erase w₂ ∪ {u} →
      Finset.univ \ S₂.biUnion id
        = (Finset.univ \ S.biUnion id).erase u ∪ {w₂} →
      blockSum G S₂ ≤ blockSum G S →
      (blockSum G S₂ = blockSum G S →
        ∃ B'' ∈ S₂, 3 ≤ (B'' ∩ G.neighborFinset w₂).card) →
      u₂ ∈ Finset.univ \ S₂.biUnion id →
      ((Finset.univ \ S₂.biUnion id) ∩ G.neighborFinset u₂).card
        ≤ 2 * (k - S.card) - 1 →
      B₂ ∈ S₂ → 3 ≤ (B₂ ∩ G.neighborFinset u₂).card →
      ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card := by
  obtain ⟨w₂, S₂, u₂, B₂, hw₂B, hw₂X, hw₂u, hP₂, hC₂, hX₂, hUb₂, hbs, _hrot,
    hheavy₂, hu₂U, hdeg₂, hB₂S₂, h3₂⟩ :=
    exists_rotate_back G k hcard hmin hS hlt hlex hnolarger hu hudeg hB hw
      hBw h3
  exact hclose w₂ S₂ u₂ B₂ hw₂B hw₂X hw₂u hP₂ hC₂ hX₂ hUb₂ hbs hheavy₂ hu₂U
    hdeg₂ hB₂S₂ h3₂

/-- **Unconditional enlargement, leftover-block sub-case.**  At a lex-max
packing, if every possible relocated hole `w₂ ∈ B.erase w` comes with a
quadrilateral block inside the relocated leftover
`(univ \ ∪S).erase u ∪ {w₂}`, the packing enlarges — no `hclose` needed
(the heavy-back condition is derived by `freed_heavy_back_of_lexmax`). -/
theorem exists_larger_of_rotate_back_of_leftover [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    {u w : V} {B : Finset V}
    (hu : u ∉ S.biUnion id) (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert u (B.erase w)))
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card)
    (hQ : ∀ w₂ ∈ B.erase w, ∃ Q : Finset V,
      G.IsQuadBlock Q ∧
      Q ⊆ (Finset.univ \ S.biUnion id).erase u ∪ {w₂}) :
    ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card :=
  exists_larger_of_hole_move_same_block hS hu hB hw hBw
    (freed_heavy_back_of_lexmax hS hlex hu hB hw hBw h3) hQ

end SimpleGraph
