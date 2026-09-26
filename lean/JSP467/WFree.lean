import JSP467.CommonNbr

/-!
# JSP-000467 — the missed vertex is always freeable

A small but load-bearing observation of Wang's switching argument (Wa10):
if an outside vertex `u` sees at least three of the four vertices of a
quadrilateral block `s` and misses `w ∈ s`, then `w` is *freeable* for `u`:
the `C₄` of `s` restricted to `s.erase w` is a path on the three neighbours
of `u`, and closing it with `u` yields a quadrilateral block
`insert u (s.erase w)`.

* `IsQuadBlock.freeable_nonneighbor` — the freeability statement.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **The non-neighbour is freeable.**  If `u ∉ s` sees at least three of
the four vertices of a quadrilateral block `s` and misses `w ∈ s`, then
`insert u (s.erase w)` is again a quadrilateral block.

The proof goes through the common-neighbour characterisation of
quadrilateral blocks: the `C₄` of `s` becomes a three-vertex path inside
`s.erase w`, and with `u` adjacent to all three of its vertices the pair
`u, m` (where `m` is the middle vertex of that path) has the two endpoints
as common neighbours. -/
theorem IsQuadBlock.freeable_nonneighbor [DecidableRel G.Adj] {s : Finset V}
    (hs : G.IsQuadBlock s) {u w : V} (hu : u ∉ s) (hw : w ∈ s)
    (hnw : ¬ G.Adj u w) (h3 : 3 ≤ (s ∩ G.neighborFinset u).card) :
    G.IsQuadBlock (insert u (s.erase w)) := by
  obtain ⟨a, b, x, y, hs4, hax, hab, hay, hbx, hxy, hby,
    e_ax, e_xb, e_by, e_ya⟩ :=
    hs.exists_cycle_distinct
  have hcard : ({a, x, b, y} : Finset V).card = 4 := hs4 ▸ hs.1
  -- The vertices of `s` missed by `u` form a subset of `{w}`.
  have hdiff : s \ (s ∩ G.neighborFinset u) = {w} := by
    have hwmem : w ∈ s \ (s ∩ G.neighborFinset u) :=
      Finset.mem_sdiff.2 ⟨hw, fun h =>
        hnw ((G.mem_neighborFinset _ _).1 (Finset.mem_inter.1 h).2)⟩
    have hcard1 : (s \ (s ∩ G.neighborFinset u)).card ≤ 1 := by
      rw [Finset.card_sdiff_of_subset Finset.inter_subset_left, hs.1]
      omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.1
      (Nat.le_antisymm hcard1 (Finset.card_pos.2 ⟨w, hwmem⟩))
    rw [hv] at hwmem
    rw [Finset.mem_singleton] at hwmem
    rw [hv, hwmem]
  -- `u` is adjacent to every vertex of `s.erase w`.
  have hsee : ∀ z ∈ s, z ≠ w → G.Adj u z := by
    intro z hz hzw
    by_contra hzu
    have hz' : z ∈ s \ (s ∩ G.neighborFinset u) :=
      Finset.mem_sdiff.2 ⟨hz, fun h =>
        hzu ((G.mem_neighborFinset _ _).1 (Finset.mem_inter.1 h).2)⟩
    rw [hdiff, Finset.mem_singleton] at hz'
    exact hzw hz'
  -- The new block has four vertices.
  have hcardQ : (insert u (s.erase w)).card = 4 := by
    have huu : u ∉ s.erase w := by
      rw [Finset.mem_erase]
      exact fun h => hu h.2
    rw [Finset.card_insert_eq_ite, if_neg huu, Finset.card_erase_of_mem hw, hs.1]
  -- `u` is not one of the vertices of the cycle.
  have hu4 : ∀ z ∈ ({a, x, b, y} : Finset V), z ≠ u := by
    intro z hz hzu
    have hz' : z ∈ s := by rw [hs4]; exact hz
    have : u ∈ s := by rw [← hzu]; exact hz'
    exact hu this
  -- Closing the path `p - m - r` inside `s.erase w` with `u` gives a block.
  have key : ∀ m p r : V, m ∈ ({a, x, b, y} : Finset V) →
      p ∈ ({a, x, b, y} : Finset V) → r ∈ ({a, x, b, y} : Finset V) →
      m ≠ w → p ≠ w → r ≠ w → G.Adj m p → G.Adj m r → p ≠ r →
      G.IsQuadBlock (insert u (s.erase w)) := by
    intro m p r hm hp hr hmw hpw hrw hmp hmr hpr
    have hms : m ∈ s := by rw [hs4]; exact hm
    have hps : p ∈ s := by rw [hs4]; exact hp
    have hrs : r ∈ s := by rw [hs4]; exact hr
    rw [IsQuadBlock.iff_two_common hcardQ]
    refine ⟨u, Finset.mem_insert_self u _, m, ?_, ?_, ?_⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hmw, hms⟩)
    · exact (hu4 m hm).symm
    · have hsub : ({p, r} : Finset V) ⊆
          insert u (s.erase w) ∩ G.neighborFinset u ∩ G.neighborFinset m := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with hzp | hzr
        · rw [hzp]
          exact Finset.mem_inter.2 ⟨Finset.mem_inter.2
            ⟨Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hpw, hps⟩),
              (G.mem_neighborFinset u p).2 (hsee p hps hpw)⟩,
            (G.mem_neighborFinset m p).2 hmp⟩
        · rw [hzr]
          exact Finset.mem_inter.2 ⟨Finset.mem_inter.2
            ⟨Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hrw, hrs⟩),
              (G.mem_neighborFinset u r).2 (hsee r hrs hrw)⟩,
            (G.mem_neighborFinset m r).2 hmr⟩
      rw [← Finset.card_pair hpr]
      exact Finset.card_le_card hsub
  -- Case on which vertex of the `C₄` is `w`; in each case `s.erase w` is a
  -- path `p - m - r` and `u - p - m - r - u` is the new `C₄`.
  rw [hs4] at hw
  have hw' : w = a ∨ w = x ∨ w = b ∨ w = y := by
    have h1 := Finset.mem_insert.mp hw
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · have h2 := Finset.mem_insert.mp h1
      rcases h2 with h2 | h2
      · exact Or.inr (Or.inl h2)
      · have h3 := Finset.mem_insert.mp h2
        rcases h3 with h3 | h3
        · exact Or.inr (Or.inr (Or.inl h3))
        · have h4 := Finset.mem_insert.mp (show w ∈ insert y ∅ from h3)
          rcases h4 with h4 | h4
          · exact Or.inr (Or.inr (Or.inr h4))
          · exact absurd h4 (by simp)
  rcases hw' with hwa | hwx | hwb | hwy
  · -- `w = a`: remaining path `x - b - y`.
    subst w
    exact key b x y (by simp) (by simp) (by simp)
      hab.symm hax.symm hay.symm e_xb.symm e_by hxy
  · -- `w = x`: remaining path `b - y - a`.
    subst w
    exact key y b a (by simp) (by simp) (by simp)
      hxy.symm hbx.symm hax e_by.symm e_ya hab.symm
  · -- `w = b`: remaining path `x - a - y`.
    subst w
    exact key a x y (by simp) (by simp) (by simp)
      hab hbx hby.symm e_ax e_ya.symm hxy
  · -- `w = y`: remaining path `a - x - b`.
    subst w
    exact key x a b (by simp) (by simp) (by simp)
      hxy hay hby e_ax.symm e_xb hab

end SimpleGraph
