import JSP467.Chord
import JSP467.Heavy
import JSP467.Exchange

/-!
# JSP-000467 — the `K₄` case of the heavy-vertex exchange

When a leftover vertex `u` is adjacent to *all four* vertices of a block `B`
in a `blockSum`-maximal packing, the chord-counting argument of
`freeable_universal_of_full` applies at every position `w ∈ B` (since
`IsQuadBlock.exchange_all` makes every vertex freeable).  The upshot: `B`
must induce a complete graph `K₄`.

* `heavy_full_block_isClique` — every pair of distinct vertices of `B` is
  adjacent.
* `exchanged_block_heavy_back` — after exchanging `u` for a universal
  `w ∈ B`, `w` still has its three neighbours inside the new block, so it
  stays heavy and can rotate back.
* `isQuadBlock_of_bip` — a four-cycle `a - x - b - y - a` packaged as a
  quadrilateral block on `{a, x, b, y}`.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- If `u` outside block `B` sees all of `B` and `S` is blockSum-maximal, then
`B` induces a `K₄`: every pair of distinct vertices of `B` is adjacent. -/
theorem heavy_full_block_isClique [DecidableRel G.Adj] {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S)
    (hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T ≤ blockSum G S)
    {u : V} (hu : u ∉ S.biUnion id) {B : Finset V} (hB : B ∈ S)
    (hadj : ∀ x ∈ B, G.Adj u x) :
    ∀ x ∈ B, ∀ y ∈ B, x ≠ y → G.Adj x y := by
  have huB : u ∉ B := fun h => hu (Finset.subset_biUnion_of_mem id hB h)
  -- Every `w ∈ B` is freeable, hence universal inside `B`.
  have hex : ∀ w ∈ B, G.IsQuadBlock (insert u (B.erase w)) :=
    IsQuadBlock.exchange_all (hS.1 B hB) huB hadj
  have huniv : ∀ w ∈ B, ∀ x ∈ B, x ≠ w → G.Adj w x :=
    fun w hw => freeable_universal_of_full hS hmax hu hB hw (hex w hw) hadj
  intro x hx y hy hxy
  exact (huniv y hy x hx hxy).symm

/-- In the exchanged packing `S'`, `u` sees all of `B' = B \ {w} ∪ {u}`'s
other vertices... precisely: `w` has ≥3 neighbours inside `B'` whenever
`w` was universal in `B` (so `w` is heavy on `B'` and can rotate back). -/
theorem exchanged_block_heavy_back [DecidableRel G.Adj] {B : Finset V}
    {u w : V} (hB4 : B.card = 4) (hw : w ∈ B) (huB : u ∉ B)
    (hwuniv : ∀ x ∈ B, x ≠ w → G.Adj w x) :
    3 ≤ ((insert u (B.erase w)) ∩ G.neighborFinset w).card := by
  -- `B.erase w` is a 3-element subset of `B' ∩ N(w)`.
  have hsub : B.erase w ⊆ (insert u (B.erase w)) ∩ G.neighborFinset w := by
    intro x hx
    obtain ⟨hxw, hxB⟩ := Finset.mem_erase.1 hx
    exact Finset.mem_inter.2 ⟨Finset.mem_insert_of_mem hx,
      (G.mem_neighborFinset w x).2 (hwuniv x hxB hxw)⟩
  have hcard : (B.erase w).card = 3 := by
    rw [Finset.card_erase_of_mem hw, hB4]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- If `x,y ∈ B` are adjacent in `G` and `a,b` are distinct leftover vertices
with `G.Adj a x`, `G.Adj a y`, `G.Adj b x`, `G.Adj b y`, then `{a,x,b,y}` and
any quad on the complementary `B ∪ U` vertices can drive
`exists_larger_of_two_blocks`.  Prove the small part: `{a, x, b, y}` is a
quad block given the cross adjacencies and distinctness. -/
theorem isQuadBlock_of_bip [DecidableRel G.Adj] {a b x y : V}
    (hab : a ≠ b) (hxy : x ≠ y) (hax : a ≠ x) (hay : a ≠ y) (hbx : b ≠ x)
    (hby : b ≠ y)
    (e1 : G.Adj a x) (e2 : G.Adj x b) (e3 : G.Adj b y) (e4 : G.Adj y a) :
    G.IsQuadBlock {a, x, b, y} := by
  -- Cycle order `a - x - b - y - a`.
  exact IsQuadBlock.of_cycle rfl hax hab hay hbx.symm hxy hby e1 e2 e3 e4

end SimpleGraph
