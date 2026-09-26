import JSP467.CaseB
import JSP467.Chord
import JSP467.Heavy
import JSP467.Rotate
import JSP467.HoleMove
import JSP467.Cascade
import JSP467.LeftoverDichotomy

/-!
# JSP-000467 — the full-seer subcase of `wang_heavy_lex`

The residual lemma `wang_heavy_lex` (Reduce.lean) concerns a
lexicographically maximal (cardinality, `blockSum`, leftover `edgeSum`)
non-covering quadrilateral packing `S` carrying a *heavy* leftover vertex
`u` — one with at least three neighbours inside a packing block `B`.  This
module develops the **full-seer** subcase `(B ∩ N u).card = 4` and its
reduction infrastructure:

* `full_seer_gives_k4_block` — at a `blockSum`-maximal packing, a leftover
  vertex adjacent to all four vertices of `B` forces `B` to span `K₄`
  (`edgeSum G B = 12`).  Packing-level mirror of `k4_of_full_seer`
  (WNine.lean).
* `exchange_biUnion_eq` — set algebra for the covered set after swapping a
  block vertex `w ∈ B` for an outside vertex `u`:
  `⋃(insert (insert u (B.erase w)) (S.erase B)) = (⋃S).erase w ∪ {u}`.
* `exchange_leftover_eq` — the leftover version:
  `univ \ ⋃S' = (univ \ ⋃S).erase u ∪ {w}`.
* `full_seer_step` — the key reduction.  At a lex-max packing under
  `hnolarger`, if `u` sees all of `B` then every `w ∈ B` is freeable
  (`exchange_all`), the exchanged packing `S' = insert (insert u (B.erase w))
  (S.erase B)` has the *same* `blockSum` (the exchanged block is again `K₄`),
  its leftover `edgeSum` does not increase, the new leftover
  `(U.erase u) ∪ {w}` is quad-free, `w` satisfies the rotation bound, and `w`
  is heavy back on the exchanged block.
* `full_seer_pingpong` — when additionally `w ~ u` and the rotation bound is
  tight, the exchanged packing is again lex-max with the same invariants and
  carries the full-seer heavy vertex `w` on the exchanged block
  `B' = insert u (B.erase w)`: the full-seer configuration recurs with the
  roles of `u` and `w` swapped.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

/-- **Full seer ⇒ `K₄` (packing version).**  At a `blockSum`-maximal
quadrilateral packing `S`, if the uncovered vertex `u` is adjacent to all
four vertices of the block `B ∈ S`, then every `w ∈ B` is universal inside
`B`, so `B` spans `K₄`: `edgeSum G B = 12`. -/
theorem full_seer_gives_k4_block {S : Finset (Finset V)} {B : Finset V} {u : V}
    (hS : G.IsQuadPacking S)
    (hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T ≤ blockSum G S)
    (hB : B ∈ S) (hu : u ∉ S.biUnion id)
    (h4 : (B ∩ G.neighborFinset u).card = 4) :
    edgeSum G B = 12 := by
  have hBq : G.IsQuadBlock B := hS.1 B hB
  have hBcard : B.card = 4 := hBq.1
  have huB : u ∉ B := fun h => hu (Finset.subset_biUnion_of_mem id hB h)
  have hadj : ∀ x ∈ B, G.Adj u x :=
    card_four_subset_neighbor_of_full hBcard h4
  -- Every `w ∈ B` is freeable (`u` sees all of `B`), hence universal in `B`.
  have huniv : ∀ w ∈ B, ∀ x ∈ B, x ≠ w → G.Adj w x := by
    intro w hw
    exact freeable_universal_of_full hS hmax hu hB hw
      (IsQuadBlock.exchange_all hBq huB hadj w hw) hadj
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

omit [Fintype V] [DecidableRel G.Adj] in
/-- **Exchange covered-set algebra.**  Swapping `w ∈ B` for the (arbitrary)
vertex `u` replaces the covered set `⋃S` by `(⋃S).erase w ∪ {u}`: the new
block is `insert u (B.erase w)` and the other blocks are untouched.  This is
the set-identity component of `IsQuadPacking.exchange_block`, available
without the block hypothesis. -/
theorem exchange_biUnion_eq {S : Finset (Finset V)} {B : Finset V} {u w : V}
    (hS : G.IsQuadPacking S) (hB : B ∈ S) (hw : w ∈ B) :
    (insert (insert u (B.erase w)) (S.erase B)).biUnion id
      = (S.biUnion id).erase w ∪ {u} := by
  have hBS : B ⊆ S.biUnion id := Finset.subset_biUnion_of_mem id hB
  -- `⋃S` splits as `B ⊔ ⋃(S.erase B)` (disjoint union).
  have hsplit : S.biUnion id = B ∪ (S.erase B).biUnion id := by
    conv_lhs => rw [← Finset.insert_erase hB]
    rw [Finset.biUnion_insert]
    rfl
  have hdisjB : Disjoint B ((S.erase B).biUnion id) := by
    rw [Finset.disjoint_biUnion_right]
    intro C hC
    obtain ⟨hCB, hCS⟩ := Finset.mem_erase.1 hC
    exact hS.2 B hB C hCS hCB.symm
  have herase : (S.erase B).biUnion id = S.biUnion id \ B := by
    rw [hsplit, Finset.union_sdiff_cancel_left hdisjB]
  -- `B.erase w ∪ (⋃S \ B) = (⋃S).erase w` since `{w} ⊆ B ⊆ ⋃S`.
  have hmerge : B.erase w ∪ (S.biUnion id \ B)
      = (S.biUnion id).erase w := by
    rw [← Finset.sdiff_singleton_eq_erase, ← Finset.sdiff_singleton_eq_erase,
      Finset.union_comm,
      Finset.sdiff_union_sdiff_cancel hBS (Finset.singleton_subset_iff.2 hw)]
  rw [Finset.biUnion_insert, herase]
  simp only [id_eq]
  rw [Finset.insert_eq, Finset.union_assoc, hmerge]
  exact Finset.union_comm _ _

omit [DecidableRel G.Adj] in
/-- **Exchange leftover algebra.**  After swapping `w ∈ B` for the uncovered
vertex `u`, the leftover of the exchanged packing is
`(univ \ ⋃S).erase u ∪ {w}`. -/
theorem exchange_leftover_eq {S : Finset (Finset V)} {B : Finset V} {u w : V}
    (hS : G.IsQuadPacking S)
    (hu : u ∉ S.biUnion id) (hB : B ∈ S) (hw : w ∈ B) :
    Finset.univ \ (insert (insert u (B.erase w)) (S.erase B)).biUnion id
      = (Finset.univ \ S.biUnion id).erase u ∪ {w} := by
  rw [exchange_biUnion_eq hS hB hw]
  exact univ_sdiff_erase_union_singleton
    (Finset.subset_biUnion_of_mem id hB hw) hu

/-- **The full-seer exchange step.**  At a lexicographically maximal packing
`S` with no enlargement, if the leftover vertex `u` sees all four vertices of
the block `B ∈ S`, then every `w ∈ B` can be exchanged for `u`, producing a
packing `S' = insert (insert u (B.erase w)) (S.erase B)` that:

* has the same cardinality and leftover `(U.erase u) ∪ {w}`;
* has the *same* `blockSum` (both `B` and the exchanged block are `K₄`), so
  the lex bound forces the leftover `edgeSum` not to increase;
* has a quad-free new leftover (else enlargement via
  `exists_larger_of_exchange_leftover_block`);
* satisfies the rotation bound
  `|N(w) ∩ (U.erase u)| ≤ |N(u) ∩ U|`; and
* leaves `w` heavy back on the exchanged block
  (`3 ≤ (B' ∩ N w).card`, `freed_heavy_back_of_lexmax`). -/
theorem full_seer_step (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    (hnolarger : ¬ ∃ T : Finset (Finset V), G.IsQuadPacking T ∧ S.card < T.card)
    {u : V} (hu : u ∈ Finset.univ \ S.biUnion id)
    {B : Finset V} (hB : B ∈ S)
    (h4 : (B ∩ G.neighborFinset u).card = 4) :
    ∀ w ∈ B, ∃ S' : Finset (Finset V),
      S' = insert (insert u (B.erase w)) (S.erase B) ∧
      G.IsQuadPacking S' ∧ S'.card = S.card ∧
      Finset.univ \ S'.biUnion id =
        (Finset.univ \ S.biUnion id).erase u ∪ {w} ∧
      blockSum G S' = blockSum G S ∧
      edgeSum G (Finset.univ \ S'.biUnion id) ≤
        edgeSum G (Finset.univ \ S.biUnion id) ∧
      ¬ G.IsQuadBlock ((Finset.univ \ S.biUnion id).erase u ∪ {w}) ∧
      ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card ≤
        ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card ∧
      3 ≤ ((insert u (B.erase w)) ∩ G.neighborFinset w).card := by
  classical
  have hu' : u ∉ S.biUnion id := (Finset.mem_sdiff.1 hu).2
  have hBq : G.IsQuadBlock B := hS.1 B hB
  have hBcard : B.card = 4 := hBq.1
  have huB : u ∉ B := fun h => hu' (Finset.subset_biUnion_of_mem id hB h)
  have hadj : ∀ x ∈ B, G.Adj u x :=
    card_four_subset_neighbor_of_full hBcard h4
  have h3 : 3 ≤ (B ∩ G.neighborFinset u).card := by omega
  -- Plain `blockSum`-maximality from the lexicographic bound.
  have hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T →
      T.card = S.card → blockSum G T ≤ blockSum G S :=
    fun T hT hTm => (hlex T hT hTm).elim le_of_lt fun h => le_of_eq h.1
  -- `B` is `K₄`.
  have hK4 : edgeSum G B = 12 := full_seer_gives_k4_block hS hmax hB hu' h4
  intro w hw
  -- `u` sees all of `B`, so every `w ∈ B` is freeable.
  have hBw : G.IsQuadBlock (insert u (B.erase w)) :=
    IsQuadBlock.exchange_all hBq huB hadj w hw
  obtain ⟨hS', hcard', hUb⟩ := hS.exchange_block hu' hB hw hBw
  have hwU : w ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB hw
  have hcov : Finset.univ \
      (insert (insert u (B.erase w)) (S.erase B)).biUnion id
      = (Finset.univ \ S.biUnion id).erase u ∪ {w} := by
    rw [hUb]
    exact univ_sdiff_erase_union_singleton hwU hu'
  -- `w` is universal inside `B` (`freeable_universal_of_full`).
  have huniv : ∀ x ∈ B, x ≠ w → G.Adj w x :=
    freeable_universal_of_full hS hmax hu' hB hw hBw hadj
  have hcap_u : B.erase w ∩ G.neighborFinset u = B.erase w :=
    Finset.inter_eq_left.2 fun x hx =>
      (G.mem_neighborFinset u x).2 (hadj x (Finset.mem_of_mem_erase hx))
  have hcap_w : B.erase w ∩ G.neighborFinset w = B.erase w :=
    Finset.inter_eq_left.2 fun x hx =>
      (G.mem_neighborFinset w x).2
        (huniv x (Finset.mem_of_mem_erase hx) (Finset.mem_erase.1 hx).1)
  have herase : (B.erase w).card = 3 := by
    rw [Finset.card_erase_of_mem hw, hBcard]
  -- The exchanged block is again `K₄`.
  have hB'edge : edgeSum G (insert u (B.erase w)) = 12 := by
    have h := edgeSum_block_exchange (G := G) B huB hw
    rw [hK4, hcap_u, hcap_w, herase] at h
    omega
  -- `blockSum` is preserved: only the exchanged block contributes the change.
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
  have hbs : blockSum G (insert (insert u (B.erase w)) (S.erase B))
      = blockSum G S := by
    rw [hsum1, hsum2, hB'edge, hK4]
  -- `blockSum` equality forces the leftover `edgeSum` bound via `hlex`.
  have hle2 : edgeSum G (Finset.univ \
      (insert (insert u (B.erase w)) (S.erase B)).biUnion id)
      ≤ edgeSum G (Finset.univ \ S.biUnion id) := by
    rcases hlex _ hS' hcard' with hlt' | ⟨-, hle⟩
    · rw [hbs] at hlt'
      exact absurd hlt' (lt_irrefl _)
    · exact hle
  -- The new leftover is quad-free, else the packing enlarges.
  have hqf : ¬ G.IsQuadBlock
      ((Finset.univ \ S.biUnion id).erase u ∪ {w}) := by
    intro hQ
    exact hnolarger (exists_larger_of_exchange_leftover_block hS hu' hB hw hBw
      hQ fun x hx => hx)
  -- The rotation bound on `w`'s reduced-leftover neighbourhood.
  have hwU' : w ∉ Finset.univ \ S.biUnion id :=
    fun h => (Finset.mem_sdiff.1 h).2 hwU
  have hrot : ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card
      ≤ ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card := by
    rw [hcov] at hle2
    rw [edgeSum_exchange _ hu hwU'] at hle2
    omega
  -- `w` is heavy back on the exchanged block.
  have hback : 3 ≤ ((insert u (B.erase w)) ∩ G.neighborFinset w).card :=
    freed_heavy_back_of_lexmax hS hlex hu' hB hw hBw h3
  exact ⟨_, rfl, hS', hcard', hcov, hbs, hle2, hqf, hrot, hback⟩

/-- **Full-seer ping-pong.**  At a lex-max packing, if the leftover vertex
`u` sees all of `B ∈ S` and the freed `w ∈ B` additionally sees `u` with a
*tight* rotation bound (`w`'s reduced-leftover degree equals `u`'s leftover
degree), then the exchanged packing `S' = insert (insert u (B.erase w))
(S.erase B)` is again lexicographically maximal — same cardinality, same
`blockSum`, same leftover `edgeSum` — and carries the full-seer heavy vertex
`w` on the exchanged block `B' = insert u (B.erase w)`: the full-seer
configuration recurs with the roles of `u` and `w` swapped. -/
theorem full_seer_pingpong (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Finset (Finset V)} (hS : G.IsQuadPacking S)
    (hlex : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T < blockSum G S ∨
        (blockSum G T = blockSum G S ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \ S.biUnion id)))
    {u w : V} (hu : u ∈ Finset.univ \ S.biUnion id)
    {B : Finset V} (hB : B ∈ S) (hw : w ∈ B)
    (h4 : (B ∩ G.neighborFinset u).card = 4)
    (hadjwu : G.Adj w u)
    (htight : ((Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset w).card
      = ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card) :
    ∃ (S' : Finset (Finset V)) (w' : V) (B' : Finset V),
      G.IsQuadPacking S' ∧ S'.card = S.card ∧
      (∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S'.card →
        blockSum G T < blockSum G S' ∨
          (blockSum G T = blockSum G S' ∧
            edgeSum G (Finset.univ \ T.biUnion id) ≤
              edgeSum G (Finset.univ \ S'.biUnion id))) ∧
      w' ∈ Finset.univ \ S'.biUnion id ∧ B' ∈ S' ∧
      (B' ∩ G.neighborFinset w').card = 4 := by
  classical
  have hu' : u ∉ S.biUnion id := (Finset.mem_sdiff.1 hu).2
  have hBq : G.IsQuadBlock B := hS.1 B hB
  have hBcard : B.card = 4 := hBq.1
  have huB : u ∉ B := fun h => hu' (Finset.subset_biUnion_of_mem id hB h)
  have hadj : ∀ x ∈ B, G.Adj u x :=
    card_four_subset_neighbor_of_full hBcard h4
  have hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T →
      T.card = S.card → blockSum G T ≤ blockSum G S :=
    fun T hT hTm => (hlex T hT hTm).elim le_of_lt fun h => le_of_eq h.1
  have hK4 : edgeSum G B = 12 := full_seer_gives_k4_block hS hmax hB hu' h4
  -- `w` is freeable (`u` sees all of `B`); form the exchanged packing.
  have hBw : G.IsQuadBlock (insert u (B.erase w)) :=
    IsQuadBlock.exchange_all hBq huB hadj w hw
  obtain ⟨hS', hcard', hUb⟩ := hS.exchange_block hu' hB hw hBw
  have hwU : w ∈ S.biUnion id := Finset.subset_biUnion_of_mem id hB hw
  have hcov : Finset.univ \
      (insert (insert u (B.erase w)) (S.erase B)).biUnion id
      = (Finset.univ \ S.biUnion id).erase u ∪ {w} := by
    rw [hUb]
    exact univ_sdiff_erase_union_singleton hwU hu'
  -- `w` is universal inside `B`, so the exchanged block is `K₄` and
  -- `blockSum` is preserved.
  have huniv : ∀ x ∈ B, x ≠ w → G.Adj w x :=
    freeable_universal_of_full hS hmax hu' hB hw hBw hadj
  have hcap_u : B.erase w ∩ G.neighborFinset u = B.erase w :=
    Finset.inter_eq_left.2 fun x hx =>
      (G.mem_neighborFinset u x).2 (hadj x (Finset.mem_of_mem_erase hx))
  have hcap_w : B.erase w ∩ G.neighborFinset w = B.erase w :=
    Finset.inter_eq_left.2 fun x hx =>
      (G.mem_neighborFinset w x).2
        (huniv x (Finset.mem_of_mem_erase hx) (Finset.mem_erase.1 hx).1)
  have herase : (B.erase w).card = 3 := by
    rw [Finset.card_erase_of_mem hw, hBcard]
  have hB'edge : edgeSum G (insert u (B.erase w)) = 12 := by
    have h := edgeSum_block_exchange (G := G) B huB hw
    rw [hK4, hcap_u, hcap_w, herase] at h
    omega
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
  have hbs : blockSum G (insert (insert u (B.erase w)) (S.erase B))
      = blockSum G S := by
    rw [hsum1, hsum2, hB'edge, hK4]
  -- Tight rotation bound ⇒ the leftover `edgeSum` is preserved.  The split
  -- `edgeSum U = edgeSum (U.erase u) + 2 * |U ∩ N u|` rules out the Nat
  -- truncated-subtraction pitfall in `edgeSum_exchange`.
  have hwU' : w ∉ Finset.univ \ S.biUnion id :=
    fun h => (Finset.mem_sdiff.1 h).2 hwU
  have hinter : (Finset.univ \ S.biUnion id).erase u ∩ G.neighborFinset u
      = (Finset.univ \ S.biUnion id) ∩ G.neighborFinset u := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase, G.mem_neighborFinset]
    constructor
    · rintro ⟨⟨-, hx⟩, hadj⟩
      exact ⟨hx, hadj⟩
    · rintro ⟨hx, hadj⟩
      refine ⟨⟨?_, hx⟩, hadj⟩
      rintro rfl
      exact G.ne_of_adj hadj rfl
  have hsplit : edgeSum G (Finset.univ \ S.biUnion id)
      = edgeSum G ((Finset.univ \ S.biUnion id).erase u)
        + 2 * ((Finset.univ \ S.biUnion id) ∩ G.neighborFinset u).card := by
    conv_lhs => rw [← Finset.insert_erase hu]
    rw [edgeSum_insert _ (Finset.notMem_erase u _), hinter]
  have hes : edgeSum G (Finset.univ \
      (insert (insert u (B.erase w)) (S.erase B)).biUnion id)
      = edgeSum G (Finset.univ \ S.biUnion id) := by
    rw [hcov, edgeSum_exchange _ hu hwU', htight]
    omega
  -- `S'` is again lexicographically maximal (same `blockSum`, same leftover
  -- `edgeSum`, same cardinality).
  have hlex' : ∀ T : Finset (Finset V), G.IsQuadPacking T →
      T.card = (insert (insert u (B.erase w)) (S.erase B)).card →
      blockSum G T
          < blockSum G (insert (insert u (B.erase w)) (S.erase B)) ∨
        (blockSum G T
            = blockSum G (insert (insert u (B.erase w)) (S.erase B)) ∧
          edgeSum G (Finset.univ \ T.biUnion id) ≤
            edgeSum G (Finset.univ \
              (insert (insert u (B.erase w)) (S.erase B)).biUnion id)) := by
    intro T hT hTm
    rcases hlex T hT (hTm.trans hcard') with hlt | ⟨heq, hle⟩
    · exact Or.inl (hbs ▸ hlt)
    · exact Or.inr ⟨hbs ▸ heq, hes ▸ hle⟩
  -- `w` is a leftover vertex of `S'`, and `B'` is a block of `S'`.
  have hwleft : w ∈ Finset.univ \
      (insert (insert u (B.erase w)) (S.erase B)).biUnion id := by
    rw [hcov]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self w)
  have hB'mem : insert u (B.erase w)
      ∈ insert (insert u (B.erase w)) (S.erase B) :=
    Finset.mem_insert_self _ _
  -- `w` sees all of `B' = insert u (B.erase w)`: `u` via `hadjwu`, the rest
  -- via `w`'s universality in `B` — the full seer recurs.
  have hfull : insert u (B.erase w) ∩ G.neighborFinset w
      = insert u (B.erase w) :=
    Finset.inter_eq_left.2 fun x hx => by
      rw [G.mem_neighborFinset]
      rcases Finset.mem_insert.1 hx with rfl | hxe
      · exact hadjwu
      · exact huniv x (Finset.mem_of_mem_erase hxe)
            (Finset.mem_erase.1 hxe).1
  have h4' : ((insert u (B.erase w)) ∩ G.neighborFinset w).card = 4 := by
    rw [hfull]; exact hBw.1
  exact ⟨_, w, _, hS', hcard', hlex', hwleft, hB'mem, h4'⟩

end SimpleGraph
