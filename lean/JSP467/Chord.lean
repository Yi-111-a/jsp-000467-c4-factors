import JSP467.Rotate
import JSP467.Exchange
import JSP467.Pairing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# JSP-000467 — chord-counting exchange machinery

Wang's second potential function: instead of the leftover edge-sum, maximise
the total *internal* edge-sum of the packing blocks (`blockSum`, twice the
chord count τ).  An exchange that swaps a leftover vertex `u` into a block
`B` in place of `w` cannot increase `blockSum`; this yields the degree
comparison `blockSum_exchange_le`, dual to `rotate_neighbor_card_le`.

The sharp corollary `freeable_universal_of_full`: if the outside vertex `u`
is adjacent to *all four* vertices of `B`, then every freeable `w ∈ B` is
universal inside `B` (adjacent to the other three block vertices).
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Total internal edge-sum of the blocks of a packing (twice Wang's chord
count τ). -/
def blockSum (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Finset V)) :
    ℕ :=
  ∑ B ∈ S, edgeSum G B

/-- Among packings of cardinality `m` there is one maximising `blockSum`. -/
theorem exists_max_blockSum_packing [DecidableRel G.Adj] (m : ℕ)
    (hne : ∃ S : Finset (Finset V), G.IsQuadPacking S ∧ S.card = m) :
    ∃ S : Finset (Finset V), G.IsQuadPacking S ∧ S.card = m ∧
      ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = m →
        blockSum G T ≤ blockSum G S := by
  classical
  set P : Finset (Finset (Finset V)) :=
    univ.filter fun S => G.IsQuadPacking S ∧ S.card = m with hPdef
  have hmem : ∀ S : Finset (Finset V),
      S ∈ P ↔ G.IsQuadPacking S ∧ S.card = m := by
    intro S
    simp [hPdef]
  obtain ⟨S₀, hS₀⟩ := hne
  have hne' : P.Nonempty := ⟨S₀, (hmem S₀).2 hS₀⟩
  obtain ⟨S, hSP, hSmax⟩ := Finset.exists_max_image P
    (fun S => blockSum G S) hne'
  exact ⟨S, ((hmem S).1 hSP).1, ((hmem S).1 hSP).2,
    fun T hT hTm => hSmax T ((hmem T).2 ⟨hT, hTm⟩)⟩

/-- Block edge-sum change under exchange: inserting `u` for erased `w`
removes twice the number of neighbours `w` had among the remaining block
vertices and adds twice the number `u` has there. -/
theorem edgeSum_block_exchange [DecidableRel G.Adj] (B : Finset V) {u w : V}
    (hu : u ∉ B) (hw : w ∈ B) :
    edgeSum G (insert u (B.erase w)) =
      edgeSum G B - 2 * ((B.erase w) ∩ G.neighborFinset w).card
        + 2 * ((B.erase w) ∩ G.neighborFinset u).card := by
  have huBw : u ∉ B.erase w := fun h => hu (Finset.mem_of_mem_erase h)
  have hinter : B.erase w ∩ G.neighborFinset w
      = B ∩ G.neighborFinset w := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase, G.mem_neighborFinset]
    constructor
    · rintro ⟨⟨_, hx⟩, hadj⟩
      exact ⟨hx, hadj⟩
    · rintro ⟨hx, hadj⟩
      refine ⟨⟨?_, hx⟩, hadj⟩
      rintro rfl
      exact G.ne_of_adj hadj rfl
  have hsplit : edgeSum G B
      = edgeSum G (B.erase w) + 2 * (B ∩ G.neighborFinset w).card := by
    conv_lhs => rw [← Finset.insert_erase hw]
    rw [edgeSum_insert (B.erase w) (Finset.notMem_erase w B), hinter]
  rw [edgeSum_insert (B.erase w) huBw, hsplit, hinter]
  omega

/-- Chord maximality ⇒ a freeable vertex `w` sees at least as many remaining
block vertices as `u` does. -/
theorem blockSum_exchange_le [DecidableRel G.Adj] {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S)
    (hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T ≤ blockSum G S)
    {u w : V} (hu : u ∉ S.biUnion id) {B : Finset V} (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert u (B.erase w))) :
    ((B.erase w) ∩ G.neighborFinset u).card ≤
      ((B.erase w) ∩ G.neighborFinset w).card := by
  have huB : u ∉ B := fun h => hu (Finset.subset_biUnion_of_mem id hB h)
  obtain ⟨hS', hcard', -⟩ := hS.exchange_block hu hB hw hBw
  have hle := hmax _ hS' hcard'
  -- The new block is genuinely new: it contains `u`, which no old block does.
  have hB'nin : insert u (B.erase w) ∉ S.erase B := by
    intro h
    exact hu (Finset.subset_biUnion_of_mem id (Finset.mem_erase.1 h).2
      (Finset.mem_insert_self u _))
  have hsum1 : blockSum G (insert (insert u (B.erase w)) (S.erase B))
      = edgeSum G (insert u (B.erase w)) + blockSum G (S.erase B) := by
    simp only [blockSum]
    exact Finset.sum_insert hB'nin
  have hsum2 : blockSum G S = edgeSum G B + blockSum G (S.erase B) := by
    simp only [blockSum]
    conv_lhs => rw [← Finset.insert_erase hB]
    rw [Finset.sum_insert (Finset.notMem_erase B S)]
  rw [hsum1, hsum2] at hle
  have hex := edgeSum_block_exchange (G := G) B huB hw
  omega

/-- Corollary (the sharp end): if `u` is adjacent to ALL of `B`, every
freeable `w ∈ B` is universal in `B` (adjacent to the other three
vertices). -/
theorem freeable_universal_of_full [DecidableRel G.Adj]
    {S : Finset (Finset V)}
    (hS : G.IsQuadPacking S)
    (hmax : ∀ T : Finset (Finset V), G.IsQuadPacking T → T.card = S.card →
      blockSum G T ≤ blockSum G S)
    {u w : V} (hu : u ∉ S.biUnion id) {B : Finset V} (hB : B ∈ S) (hw : w ∈ B)
    (hBw : G.IsQuadBlock (insert u (B.erase w)))
    (hadj : ∀ x ∈ B, G.Adj u x) :
    ∀ x ∈ B, x ≠ w → G.Adj w x := by
  have hle := blockSum_exchange_le hS hmax hu hB hw hBw
  have hBcard : B.card = 4 := (hS.1 B hB).1
  have herase : (B.erase w).card = 3 := by
    rw [Finset.card_erase_of_mem hw, hBcard]
  -- All of `B.erase w` lies in the neighbourhood of `u`.
  have hsub : B.erase w ⊆ G.neighborFinset u := by
    intro x hx
    exact (G.mem_neighborFinset u x).2
      (hadj x (Finset.mem_of_mem_erase hx))
  have hcap : B.erase w ∩ G.neighborFinset u = B.erase w :=
    Finset.inter_eq_left.2 hsub
  rw [hcap, herase] at hle
  -- `(B.erase w) ∩ N w` is a 3-element subset of the 3-element `B.erase w`.
  have heq : B.erase w ∩ G.neighborFinset w = B.erase w :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [herase]; exact hle)
  intro x hx hxw
  have hxn : x ∈ B.erase w ∩ G.neighborFinset w := by
    rw [heq]
    exact Finset.mem_erase.2 ⟨hxw, hx⟩
  exact (G.mem_neighborFinset w x).1 (Finset.mem_inter.1 hxn).2

end SimpleGraph
