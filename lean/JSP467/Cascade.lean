import JSP467.Chain2
import JSP467.LowHeavy

/-!
# JSP-000467 — bookkeeping for the switching cascade under "no enlargement"

Under the standing hypothesis `hnolarger` — no strictly larger quadrilateral
packing exists — each exchange step of Wang's argument *produces the data for
the next step*: after swapping a low-leftover-degree heavy vertex `u` for a
freeable `w ∈ B`, the new packing `S'` has the same cardinality, hence is
still non-covering and admits no enlargement either, so
`exists_heavy_lowdeg_of_no_larger` applies again and yields the next heavy
vertex `u'` in the new leftover `U' = (U.erase u) ∪ {w}`.

* `no_larger_of_card_eq` — `hnolarger` transfers across equal-cardinality
  packings.
* `heavy_lowdeg_step` — the packaged output of
  `exists_heavy_lowdeg_of_no_larger`: a leftover vertex of low leftover
  degree that is heavy on some block.
* `freed_vertex_heavy` — one full cascade step: exchange `u ↔ w` at `B`
  (keeping the explicit form `S' = insert (insert u (B.erase w)) (S.erase B)`
  available), then find the next low-leftover-degree heavy vertex `u'` with
  its heavy block `B' ∈ S'`.
* `same_or_other_block` — the new heavy block `B' ∈ S'` is either the
  exchanged block `insert u (B.erase w)` or an old block `B₂ ∈ S`, `B₂ ≠ B`.
* `freed_w_heavy_of_rotBound` — when `blockSum` is preserved, the rotation
  bound transfers `u`'s low leftover degree to the freed `w`, which is then
  itself heavy on some block of `S'` (pigeonhole via `exists_heavy_block`).
* `edgeSum_iterate_bound` — `same_or_other_block` refined by the conditional
  heaviness of `w`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `hnolarger` transfers across packings of equal cardinality. -/
theorem no_larger_of_card_eq {G : SimpleGraph V} {S S' : Finset (Finset V)}
    (hcard : S'.card = S.card)
    (hnolarger : ¬ ∃ T : Finset (Finset V),
      G.IsQuadPacking T ∧ S.card < T.card) :
    ¬ ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S'.card < T.card := by
  rintro ⟨T, hT, hTc⟩
  exact hnolarger ⟨T, hT, by omega⟩

/-- **Packaged low-leftover-degree heavy vertex.**  Under `hnolarger`, a
non-covering packing `S` has a leftover vertex `u ∈ U = univ \ ⋃S` whose
leftover degree is at most `2 * (k - S.card) - 1` and which has `≥ 3`
neighbours in some block `B ∈ S`. -/
theorem heavy_lowdeg_step (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) (hlt : S.card < k)
    (_hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    (hnolarger : ¬ ∃ T : Finset (Finset V),
      G.IsQuadPacking T ∧ S.card < T.card) :
    ∃ u : V, u ∈ Finset.univ \ S.biUnion id ∧
      ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card
        ≤ 2 * (k - S.card) - 1 ∧
      ∃ B ∈ S, 3 ≤ (B ∩ G.neighborFinset u).card :=
  exists_heavy_lowdeg_of_no_larger G k hcard hmin hS hlt hnolarger

/-- **One full cascade step.**  At a lex-max packing under `hnolarger`,
exchanging the leftover vertex `u` (heavy on `B`) for a freeable `w ∈ B`
yields a same-cardinality packing `S'` — explicitly
`insert (insert u (B.erase w)) (S.erase B)` — to which `hnolarger` transfers
(`no_larger_of_card_eq`), so `exists_heavy_lowdeg_of_no_larger` applies at
`S'` and produces the next heavy vertex `u' ∈ U' = (U.erase u) ∪ {w}` with
its heavy block `B' ∈ S'`: the cascade continues. -/
theorem freed_vertex_heavy (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) (hlt : S.card < k)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    (hnolarger : ¬ ∃ T : Finset (Finset V),
      G.IsQuadPacking T ∧ S.card < T.card)
    {u : V} (hu : u ∈ Finset.univ \ S.biUnion id)
    {B : Finset V} (hB : B ∈ S)
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    ∃ (w : V) (S' : Finset (Finset V)) (u' : V) (B' : Finset V),
      S' = insert (insert u (B.erase w)) (S.erase B) ∧
      G.IsQuadPacking S' ∧ S'.card = S.card ∧
      Finset.univ \ S'.biUnion id
        = (Finset.univ \ S.biUnion id).erase u ∪ {w} ∧
      w ∈ B ∧ w ≠ u ∧
      blockSum G S' ≤ blockSum G S ∧
      (blockSum G S' = blockSum G S →
        ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card ≤
          ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card) ∧
      u' ∈ Finset.univ \ S'.biUnion id ∧
      ((Finset.univ \ S'.biUnion id) ∩ G.neighborFinset u').card
        ≤ 2 * (k - S'.card) - 1 ∧
      B' ∈ S' ∧ 3 ≤ (B' ∩ G.neighborFinset u').card := by
  classical
  have hu' : u ∉ S.biUnion id := (Finset.mem_sdiff.1 hu).2
  have huB : u ∉ B := fun h => hu' (Finset.subset_biUnion_of_mem id hB h)
  -- Pick the first of the two freeable vertices of `B`.
  obtain ⟨w, _w₂, hwB, -, -, hBw, -⟩ :=
    exists_two_freeable (hS.1 B hB) huB h3
  have hwU : w ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB hwB
  have hne : w ≠ u := fun h => hu' (h ▸ hwU)
  -- The exchanged packing, with `S'` kept in explicit form.
  obtain ⟨hS', hcard', hUb⟩ := hS.exchange_block hu' hB hwB hBw
  obtain ⟨hle1, hrot⟩ := lexmax_exchange hS hlex hu hB hwB hBw
  -- `blockSum` splits off the exchanged block on both sides.
  have hB'nin : insert u (B.erase w) ∉ S.erase B := by
    intro h
    exact hu' (Finset.subset_biUnion_of_mem id (Finset.mem_erase.1 h).2
      (Finset.mem_insert_self u _))
  have hsum1 : blockSum G (insert (insert u (B.erase w)) (S.erase B))
      = edgeSum G (insert u (B.erase w)) + blockSum G (S.erase B) := by
    simp only [blockSum]
    exact Finset.sum_insert hB'nin
  have hsum2 : blockSum G S
      = edgeSum G B + blockSum G (S.erase B) := by
    simp only [blockSum]
    conv_lhs => rw [← Finset.insert_erase hB]
    rw [Finset.sum_insert (Finset.notMem_erase B S)]
  have hsumle : blockSum G (insert (insert u (B.erase w)) (S.erase B))
      ≤ blockSum G S := by omega
  set S' := insert (insert u (B.erase w)) (S.erase B) with hS'def
  -- `hnolarger` transfers to `S'` (same cardinality), and `S'` is still
  -- non-covering, so the low-degree-heavy dichotomy applies at `S'`.
  have hnolarger' : ¬ ∃ T : Finset (Finset V),
      G.IsQuadPacking T ∧ S'.card < T.card :=
    no_larger_of_card_eq hcard' hnolarger
  have hlt' : S'.card < k := by omega
  obtain ⟨u', hu'U, hdeg', B', hB'S', h3'⟩ :=
    exists_heavy_lowdeg_of_no_larger G k hcard hmin hS' hlt' hnolarger'
  have hcov : Finset.univ \ S'.biUnion id
      = (Finset.univ \ S.biUnion id).erase u ∪ {w} := by
    rw [hUb]
    exact univ_sdiff_erase_union_singleton hwU hu'
  have hrotb : blockSum G S' = blockSum G S →
      ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card ≤
        ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card := by
    intro heq
    exact hrot (by omega)
  exact ⟨w, S', u', B', hS'def, hS', hcard', hcov, hwB, hne, hsumle, hrotb,
    hu'U, hdeg', hB'S', h3'⟩

/-- **The new heavy block is new or old.**  In the cascade step, the heavy
block `B' ∈ S'` of the next vertex `u'` is either the exchanged block
`insert u (B.erase w)` or an old block `B₂ ∈ S` with `B₂ ≠ B`. -/
theorem same_or_other_block (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) (hlt : S.card < k)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    (hnolarger : ¬ ∃ T : Finset (Finset V),
      G.IsQuadPacking T ∧ S.card < T.card)
    {u : V} (hu : u ∈ Finset.univ \ S.biUnion id)
    {B : Finset V} (hB : B ∈ S)
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    ∃ (w u' : V),
      w ∈ B ∧ w ≠ u ∧
      G.IsQuadPacking (insert (insert u (B.erase w)) (S.erase B)) ∧
      (insert (insert u (B.erase w)) (S.erase B)).card = S.card ∧
      Finset.univ \ (insert (insert u (B.erase w)) (S.erase B)).biUnion id
        = (Finset.univ \ S.biUnion id).erase u ∪ {w} ∧
      u' ∈ Finset.univ
        \ (insert (insert u (B.erase w)) (S.erase B)).biUnion id ∧
      ((Finset.univ
          \ (insert (insert u (B.erase w)) (S.erase B)).biUnion id)
          ∩ G.neighborFinset u').card ≤ 2 * (k - S.card) - 1 ∧
      (3 ≤ ((insert u (B.erase w)) ∩ G.neighborFinset u').card ∨
        ∃ B₂ ∈ S, B₂ ≠ B ∧ 3 ≤ (B₂ ∩ G.neighborFinset u').card) := by
  classical
  obtain ⟨w, S', u', B', hS'eq, hS', hcard', hUb, hwB, hwne, _hsum, _hrot,
    hu'U, hdeg', hB'S', h3'⟩ :=
    freed_vertex_heavy G k hcard hmin hS hlt hlex hnolarger hu hB h3
  subst hS'eq
  refine ⟨w, u', hwB, hwne, hS', hcard', hUb, hu'U, ?_, ?_⟩
  · rwa [hcard'] at hdeg'
  · rcases Finset.mem_insert.1 hB'S' with hBB | hBold
    · -- `B'` is the exchanged block `insert u (B.erase w)`.
      exact Or.inl (hBB ▸ h3')
    · -- `B'` is an old block `B₂ ∈ S`, `B₂ ≠ B`.
      obtain ⟨hB'ne, hB'S⟩ := Finset.mem_erase.1 hBold
      exact Or.inr ⟨B', hB'S, hB'ne, h3'⟩

/-- **The freed vertex is heavy when the rotation bound holds.**  If `w`
inherited `u`'s low leftover-degree bound (which happens when the exchange
preserves `blockSum`), then `w`'s covered-neighbour count exceeds
`2 * S'.card` and pigeonholes into a block of `S'`. -/
theorem freed_w_heavy_of_rotBound (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hmin : 2 * k ≤ G.minDegree)
    {S S' : Finset (Finset V)} (hS' : G.IsQuadPacking S')
    (hcard' : S'.card = S.card) (hlt : S.card < k)
    {u w : V}
    (hcov : Finset.univ \ S'.biUnion id
      = (Finset.univ \ S.biUnion id).erase u ∪ {w})
    (hrot : ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card
      ≤ 2 * (k - S.card) - 1) :
    ∃ B' ∈ S', 3 ≤ (B' ∩ G.neighborFinset w).card := by
  classical
  -- Every neighbour of `w` is covered by `S'` or lies in the new leftover.
  have hsub : G.neighborFinset w
      ⊆ ((Finset.univ \ S'.biUnion id) ∩ G.neighborFinset w)
        ∪ (S'.biUnion id ∩ G.neighborFinset w) := by
    intro x hx
    by_cases hxB : x ∈ S'.biUnion id
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_inter.2 ⟨hxB, hx⟩))
    · exact Finset.mem_union.2 (Or.inl (Finset.mem_inter.2
        ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ x, hxB⟩, hx⟩))
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le
    ((Finset.univ \ S'.biUnion id) ∩ G.neighborFinset w)
    (S'.biUnion id ∩ G.neighborFinset w)
  have hdegw : 2 * k ≤ (G.neighborFinset w).card :=
    hmin.trans (G.minDegree_le_degree w)
  -- The new leftover is `(U.erase u) ∪ {w}`, and `w` is not adjacent to
  -- itself, so `w`'s leftover neighbours lie inside `U.erase u`.
  have hsub2 : (Finset.univ \ S'.biUnion id) ∩ G.neighborFinset w
      ⊆ (Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w := by
    intro x hx
    obtain ⟨hxU', hxw⟩ := Finset.mem_inter.1 hx
    rw [hcov, Finset.mem_union, Finset.mem_singleton] at hxU'
    rcases hxU' with hx | rfl
    · exact Finset.mem_inter.2 ⟨hx, hxw⟩
    · exact absurd hxw (fun h => G.ne_of_adj h rfl)
  have h3 := Finset.card_le_card hsub2
  -- `w` has at least `2k - (2 * (k - S.card) - 1) = 2 * S.card + 1`
  -- covered neighbours.
  apply exists_heavy_block hS'
  omega

/-- **Iterated bound.**  The `same_or_other_block` data, refined by the
conditional that whenever the exchange preserves `blockSum`, the freed `w`
is itself heavy on some block of `S'` — either `u' = w` can serve as the
next cascade vertex or a genuinely different `u'` does. -/
theorem edgeSum_iterate_bound (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hcard : Fintype.card V = 4 * k) (hmin : 2 * k ≤ G.minDegree)
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S) (hlt : S.card < k)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    (hnolarger : ¬ ∃ T : Finset (Finset V),
      G.IsQuadPacking T ∧ S.card < T.card)
    {u : V} (hu : u ∈ Finset.univ \ S.biUnion id)
    (hudeg : ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card
      ≤ 2 * (k - S.card) - 1)
    {B : Finset V} (hB : B ∈ S)
    (h3 : 3 ≤ (B ∩ G.neighborFinset u).card) :
    ∃ (w u' : V),
      w ∈ B ∧ w ≠ u ∧
      G.IsQuadPacking (insert (insert u (B.erase w)) (S.erase B)) ∧
      (insert (insert u (B.erase w)) (S.erase B)).card = S.card ∧
      Finset.univ \ (insert (insert u (B.erase w)) (S.erase B)).biUnion id
        = (Finset.univ \ S.biUnion id).erase u ∪ {w} ∧
      u' ∈ Finset.univ
        \ (insert (insert u (B.erase w)) (S.erase B)).biUnion id ∧
      ((Finset.univ
          \ (insert (insert u (B.erase w)) (S.erase B)).biUnion id)
          ∩ G.neighborFinset u').card ≤ 2 * (k - S.card) - 1 ∧
      (3 ≤ ((insert u (B.erase w)) ∩ G.neighborFinset u').card ∨
        ∃ B₂ ∈ S, B₂ ≠ B ∧ 3 ≤ (B₂ ∩ G.neighborFinset u').card) ∧
      (blockSum G (insert (insert u (B.erase w)) (S.erase B))
          = blockSum G S →
        ∃ B'' ∈ insert (insert u (B.erase w)) (S.erase B),
          3 ≤ (B'' ∩ G.neighborFinset w).card) := by
  classical
  obtain ⟨w, S', u', B', hS'eq, hS', hcard', hUb, hwB, hwne, _hsum, hrot,
    hu'U, hdeg', hB'S', h3'⟩ :=
    freed_vertex_heavy G k hcard hmin hS hlt hlex hnolarger hu hB h3
  subst hS'eq
  refine ⟨w, u', hwB, hwne, hS', hcard', hUb, hu'U, ?_, ?_, fun heq => ?_⟩
  · rwa [hcard'] at hdeg'
  · rcases Finset.mem_insert.1 hB'S' with hBB | hBold
    · exact Or.inl (hBB ▸ h3')
    · obtain ⟨hB'ne, hB'S⟩ := Finset.mem_erase.1 hBold
      exact Or.inr ⟨B', hB'S, hB'ne, h3'⟩
  · -- `blockSum` preserved: the rotation bound upgrades `u`'s low leftover
    -- degree to `w`, which is then itself heavy on some block of `S'`.
    apply freed_w_heavy_of_rotBound G k hmin hS' hcard' hlt hUb
    exact (hrot heq).trans hudeg

end SimpleGraph
