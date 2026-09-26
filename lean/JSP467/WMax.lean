import JSP467.WCover

/-!
# JSP-000467 — the edge-maximal reduction

A finite graph without a spanning quadrilateral factor can be enlarged,
edge by edge, to an *edge-maximal* counterexample: a supergraph `H ≥ G`,
still without a quadrilateral factor, in which the addition of any missing
edge `u - v` creates a quadrilateral factor
(`exists_edgeMaximal_factorFree`).

For such a maximal counterexample each missing edge `u - v` supplies a
*cover*: a quadrilateral packing together with the 4-vertex leftover
`U = {u, a, b, v}` that carries the `P₄` `u - a - b - v` — the `C₄` through
the added edge, minus that edge (`cover_of_added_edge_factor`).  The
single-edge supergraph is `addEdge`; `cover_exists_of_edgeMax` packages
the two statements for an edge-maximal non-complete graph.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- The supergraph obtained from `G` by adding the single edge `u - v`. -/
def addEdge (G : SimpleGraph V) (u v : V) : SimpleGraph V :=
  fromEdgeSet {s(u, v)} ⊔ G

variable {G}

instance instDecidableRelAddEdge {G : SimpleGraph V} [DecidableRel G.Adj]
    (u v : V) : DecidableRel (addEdge G u v).Adj :=
  inferInstanceAs (DecidableRel (fromEdgeSet {s(u, v)} ⊔ G).Adj)

omit [Fintype V] [DecidableEq V] in
/-- Adjacency in the one-edge supergraph: either the new edge or an old one. -/
theorem addEdge_adj {u v a b : V} :
    (addEdge G u v).Adj a b ↔ (s(a, b) = s(u, v) ∧ a ≠ b) ∨ G.Adj a b := by
  show ((fromEdgeSet {s(u, v)} ⊔ G).Adj a b) ↔ _
  rw [sup_adj, fromEdgeSet_adj, Set.mem_singleton_iff]

omit [Fintype V] [DecidableEq V] in
/-- `G` is a subgraph of its one-edge supergraph. -/
theorem le_addEdge (u v : V) : G ≤ addEdge G u v := le_sup_right

omit [Fintype V] [DecidableEq V] in
/-- The added edge is present in the supergraph. -/
theorem addEdge_adj_left {u v : V} (h : u ≠ v) : (addEdge G u v).Adj u v :=
  addEdge_adj.2 (Or.inl ⟨rfl, h⟩)

omit [Fintype V] [DecidableEq V] in
/-- An adjacency of the supergraph between endpoints different from `u - v`
already holds in `G`. -/
theorem Adj.of_addEdge {u v a b : V} (h : (addEdge G u v).Adj a b)
    (hne : s(a, b) ≠ s(u, v)) : G.Adj a b := by
  rcases addEdge_adj.1 h with ⟨hsym, -⟩ | hG
  · exact absurd hsym hne
  · exact hG

/-- **Edge-maximal factor-free supergraph.**  Maximizing the edge count among
the factor-free supergraphs of `G` (a nonempty finite family containing `G`)
yields an `H` in which every further edge creates a quadrilateral factor. -/
theorem exists_edgeMaximal_factorFree (hG : ¬ G.HasQuadFactor) :
    ∃ H : SimpleGraph V, G ≤ H ∧ ¬ H.HasQuadFactor ∧
      ∀ u v : V, u ≠ v → ¬ H.Adj u v → (addEdge H u v).HasQuadFactor := by
  classical
  set P : Finset (SimpleGraph V) :=
    univ.filter fun H => G ≤ H ∧ ¬ H.HasQuadFactor with hPdef
  have hmem : ∀ H : SimpleGraph V, H ∈ P ↔ G ≤ H ∧ ¬ H.HasQuadFactor := by
    intro H
    simp [hPdef]
  have hne : P.Nonempty := ⟨G, (hmem G).2 ⟨le_rfl, hG⟩⟩
  obtain ⟨H, hHP, hHmax⟩ :=
    Finset.exists_max_image P (fun H => Set.ncard H.edgeSet) hne
  obtain ⟨hGH, hH⟩ := (hmem H).1 hHP
  refine ⟨H, hGH, hH, fun u v huv hnadj => ?_⟩
  by_contra hfac
  have hle : H ≤ addEdge H u v := le_addEdge u v
  have hlt : H < addEdge H u v := by
    rw [lt_iff_le_and_ne]
    exact ⟨hle, fun h => hnadj (h ▸ addEdge_adj_left (G := H) huv)⟩
  have hcardlt : Set.ncard H.edgeSet < Set.ncard (addEdge H u v).edgeSet :=
    Set.ncard_lt_ncard (edgeSet_ssubset_edgeSet.2 hlt) (Set.toFinite _)
  have hmem' : addEdge H u v ∈ P :=
    (hmem _).2 ⟨le_trans hGH hle, hfac⟩
  have hcle : Set.ncard (addEdge H u v).edgeSet ≤ Set.ncard H.edgeSet :=
    hHmax _ hmem'
  omega

/-- **Cover from an added edge.**  If `u - v` is a non-edge of the
factor-free `G` whose addition creates a quadrilateral factor, then the
block `Q` containing `u` in a factor of `addEdge G u v` must use the new
edge (else `Q`, like every other block, would already be a `G`-quad and `G`
would have a factor).  Removing `u - v` from that `C₄` leaves the `P₄`
`u - a - b - v` on the leftover `U = Q`, and the remaining blocks form a
cover of `G`. -/
theorem cover_of_added_edge_factor {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hfac : (addEdge G u v).HasQuadFactor) (hG : ¬ G.HasQuadFactor) :
    ∃ S : Finset (Finset V), ∃ U : Finset V,
      G.IsCover S U ∧ u ∈ U ∧ v ∈ U ∧ ¬ G.Adj u v ∧
        ∃ a b : V, U = {u, a, b, v} ∧ G.Adj u a ∧ G.Adj a b ∧ G.Adj b v := by
  classical
  obtain ⟨S', hblk, hpair, hcov⟩ := hfac
  -- The block `Q` of the new factor containing `u`.
  have huU : u ∈ S'.biUnion id := by rw [hcov]; exact Finset.mem_univ u
  rw [Finset.mem_biUnion] at huU
  obtain ⟨Q, hQS', huQ⟩ := huU
  obtain ⟨hQcard, ⟨f⟩⟩ := hblk Q hQS'
  -- Parametrize `Q` cyclically as `x 0, x 1, x 2, x 3` via the `C₄` copy.
  set x : Fin 4 → V := fun i => (f i).1 with hxdef
  have hxQ : ∀ i : Fin 4, x i ∈ Q := fun i => Finset.mem_coe.1 (f i).2
  have hinj : Function.Injective x := fun i j h => f.injective (Subtype.ext h)
  have hcyc : ∀ p q : Fin 4, (cycleGraph 4).Adj p q →
      (addEdge G u v).Adj (x p) (x q) :=
    fun p q h => induce_adj.1 (f.toHom.map_adj h)
  have hQimg : Q = Finset.univ.image x := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · rw [Finset.image_subset_iff]
      exact fun i _ => hxQ i
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
        Fintype.card_fin, hQcard]
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (hQimg ▸ huQ)
  -- The four consecutive cycle adjacencies, in the order starting at `i`.
  have e01 : (cycleGraph 4).Adj i (i + 1) := by fin_cases i <;> decide
  have e12 : (cycleGraph 4).Adj (i + 1) (i + 2) := by fin_cases i <;> decide
  have e23 : (cycleGraph 4).Adj (i + 2) (i + 3) := by fin_cases i <;> decide
  have e30 : (cycleGraph 4).Adj (i + 3) i := by fin_cases i <;> decide
  have hs4 : ∀ k : Fin 4, Q = {x k, x (k + 1), x (k + 2), x (k + 3)} := by
    intro k
    have hU : (Finset.univ : Finset (Fin 4)) = {k, k + 1, k + 2, k + 3} := by
      fin_cases k <;> decide
    rw [hQimg, hU]
    simp [Finset.image_insert, Finset.image_singleton]
  -- A cycle edge different from `{u, v}` is already a `G`-edge.
  have hG_of_ne_edge : ∀ p q : Fin 4, (cycleGraph 4).Adj p q →
      s(x p, x q) ≠ s(u, v) → G.Adj (x p) (x q) := by
    intro p q hadj hne
    rcases addEdge_adj.1 (hcyc p q hadj) with ⟨hsym, -⟩ | hG'
    · exact absurd hsym hne
    · exact hG'
  -- If all four consecutive cycle edges are `G`-edges, `Q` is a `G`-quad.
  have hquadG_of : G.Adj (x i) (x (i + 1)) → G.Adj (x (i + 1)) (x (i + 2)) →
      G.Adj (x (i + 2)) (x (i + 3)) → G.Adj (x (i + 3)) (x i) →
      G.IsQuadBlock Q := by
    intro e1 e2 e3 e4
    have hne : ∀ k : Fin 4,
        k ≠ k + 1 ∧ k ≠ k + 2 ∧ k ≠ k + 3 ∧
          k + 1 ≠ k + 2 ∧ k + 1 ≠ k + 3 ∧ k + 2 ≠ k + 3 := by
      intro k; fin_cases k <;> decide
    exact IsQuadBlock.of_cycle (hs4 i)
      (hinj.ne (hne i).1) (hinj.ne (hne i).2.1) (hinj.ne (hne i).2.2.1)
      (hinj.ne (hne i).2.2.2.1) (hinj.ne (hne i).2.2.2.2.1)
      (hinj.ne (hne i).2.2.2.2.2) e1 e2 e3 e4
  -- Any block `T ≠ Q` avoids `u`, so its `C₄` copy cannot use the new edge:
  -- `T` is already a quadrilateral block of `G`.
  have hGquad : ∀ T ∈ S', T ≠ Q → G.IsQuadBlock T := by
    intro T hT hTQ
    have hdis : Disjoint T Q := hpair T hT Q hQS' hTQ
    have huT : u ∉ T := fun huT => Finset.disjoint_left.1 hdis huT huQ
    obtain ⟨hTc, ⟨fT⟩⟩ := hblk T hT
    refine ⟨hTc, ⟨?_⟩⟩
    refine ⟨⟨fun k => fT k, ?_⟩, fT.injective'⟩
    intro p q hadj
    rw [induce_adj]
    have hG'adj : (addEdge G u v).Adj (fT p).1 (fT q).1 :=
      induce_adj.1 (fT.toHom.map_adj hadj)
    refine Adj.of_addEdge hG'adj ?_
    intro hsym
    rw [Sym2.eq_iff] at hsym
    rcases hsym with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact huT (Finset.mem_coe.1 (h1 ▸ (fT p).2))
    · exact huT (Finset.mem_coe.1 (h2 ▸ (fT q).2))
  -- Hence `Q` itself cannot be a `G`-quad (otherwise `G` has a factor).
  have hfactor_of_QG : G.IsQuadBlock Q → G.HasQuadFactor := by
    intro hQG
    refine ⟨S', ?_, hpair, hcov⟩
    intro T hT
    by_cases hTQ : T = Q
    · subst hTQ; exact hQG
    · exact hGquad T hT hTQ
  -- `v` lies in `Q`: otherwise every cycle edge of `Q` avoids `{u, v}`.
  have hvQ : v ∈ Q := by
    by_contra hvnot
    have huv_ne : ∀ p q : Fin 4, s(x p, x q) ≠ s(u, v) := by
      intro p q hsym
      rw [Sym2.eq_iff] at hsym
      rcases hsym with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hvnot (h2 ▸ hxQ q)
      · exact hvnot (h1 ▸ hxQ p)
    exact hG (hfactor_of_QG (hquadG_of
      (hG_of_ne_edge _ _ e01 (huv_ne _ _))
      (hG_of_ne_edge _ _ e12 (huv_ne _ _))
      (hG_of_ne_edge _ _ e23 (huv_ne _ _))
      (hG_of_ne_edge _ _ e30 (huv_ne _ _))))
  obtain ⟨j, -, hj⟩ := Finset.mem_image.1 (hQimg ▸ hvQ)
  have hij : i ≠ j := fun h => huv (by rw [← hi, h, hj] : u = v)
  -- An `{x p, x q}` equal to `{u, v}` forces `{p, q} = {i, j}`.
  have hsym_imp : ∀ p q : Fin 4, s(x p, x q) = s(u, v) →
      (p = i ∧ q = j) ∨ (p = j ∧ q = i) := by
    intro p q hsym
    rw [Sym2.eq_iff] at hsym
    rcases hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hinj (h1.trans hi.symm), hinj (h2.trans hj.symm)⟩
    · exact Or.inr ⟨hinj (h1.trans hj.symm), hinj (h2.trans hi.symm)⟩
  -- The packing part of the cover (needed in both non-antipodal cases).
  have hS_pack : G.IsQuadPacking (S'.erase Q) := by
    refine ⟨?_, ?_⟩
    · intro T hT
      obtain ⟨hTQ, hTS'⟩ := Finset.mem_erase.1 hT
      exact hGquad T hTS' hTQ
    · intro s hs t ht hst
      exact hpair s (Finset.mem_erase.1 hs).2 t (Finset.mem_erase.1 ht).2 hst
  have hS_disj : Disjoint ((S'.erase Q).biUnion id) Q := by
    rw [Finset.disjoint_biUnion_left]
    intro T hT
    obtain ⟨hTQ, hTS'⟩ := Finset.mem_erase.1 hT
    exact hpair T hTS' Q hQS' hTQ
  have hS_cov : (S'.erase Q).biUnion id ∪ Q = Finset.univ := by
    have hcov' := hcov
    rw [← Finset.insert_erase hQS', Finset.biUnion_insert] at hcov'
    rwa [Finset.union_comm]
  -- `v` sits at an index `j` next to `i` on the cycle.
  have hUniv : (Finset.univ : Finset (Fin 4)) = {i, i + 1, i + 2, i + 3} := by
    fin_cases i <;> decide
  have hjmem : j ∈ ({i, i + 1, i + 2, i + 3} : Finset (Fin 4)) := by
    rw [← hUniv]; exact Finset.mem_univ j
  simp only [Finset.mem_insert, Finset.mem_singleton] at hjmem
  rcases hjmem with hji | hji1 | hji2 | hji3
  · exact absurd hji.symm hij
  · -- `v = x (i + 1)`: the cycle is `u - v - x(i+2) - x(i+3) - u`; removing
    -- `u - v` leaves the path `u - x(i+3) - x(i+2) - v`.
    subst hji1
    have hne0 : s(x (i + 3), x i) ≠ s(u, v) := by
      intro hsym
      rcases hsym_imp _ _ hsym with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 (by fin_cases i <;> decide)
      · exact absurd h1 (by fin_cases i <;> decide)
    have hne1 : s(x (i + 2), x (i + 3)) ≠ s(u, v) := by
      intro hsym
      rcases hsym_imp _ _ hsym with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 (by fin_cases i <;> decide)
      · exact absurd h1 (by fin_cases i <;> decide)
    have hne2 : s(x (i + 1), x (i + 2)) ≠ s(u, v) := by
      intro hsym
      rcases hsym_imp _ _ hsym with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 (by fin_cases i <;> decide)
      · exact absurd h2 (by fin_cases i <;> decide)
    refine ⟨S'.erase Q, Q, ⟨hS_pack, hQcard, hS_disj, hS_cov⟩,
      huQ, hvQ, hnadj, x (i + 3), x (i + 2), ?_, ?_, ?_, ?_⟩
    · rw [hs4 i, ← hi, ← hj]
      ext w
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    · rw [← hi]
      exact (hG_of_ne_edge _ _ e30 hne0).symm
    · exact (hG_of_ne_edge _ _ e23 hne1).symm
    · rw [← hj]
      exact (hG_of_ne_edge _ _ e12 hne2).symm
  · -- `v = x (i + 2)` is antipodal to `u`: no cycle edge is `{u, v}`, so `Q`
    -- would already be a `G`-quad — a contradiction.
    subst hji2
    have key : ∀ p q : Fin 4, (cycleGraph 4).Adj p q →
        s(x p, x q) ≠ s(u, v) := by
      intro p q hadj hsym
      rcases hsym_imp _ _ hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at hadj
        exact absurd hadj (by fin_cases i <;> decide)
      · rw [h1, h2] at hadj
        exact absurd hadj (by fin_cases i <;> decide)
    exact absurd (hfactor_of_QG (hquadG_of
      (hG_of_ne_edge _ _ e01 (key _ _ e01))
      (hG_of_ne_edge _ _ e12 (key _ _ e12))
      (hG_of_ne_edge _ _ e23 (key _ _ e23))
      (hG_of_ne_edge _ _ e30 (key _ _ e30)))) hG
  · -- `v = x (i + 3)`: the cycle is `u - x(i+1) - x(i+2) - v - u`; removing
    -- `u - v` leaves the path `u - x(i+1) - x(i+2) - v`.
    subst hji3
    have hne0 : s(x i, x (i + 1)) ≠ s(u, v) := by
      intro hsym
      rcases hsym_imp _ _ hsym with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact absurd h2 (by fin_cases i <;> decide)
      · exact absurd h1 (by fin_cases i <;> decide)
    have hne1 : s(x (i + 1), x (i + 2)) ≠ s(u, v) := by
      intro hsym
      rcases hsym_imp _ _ hsym with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 (by fin_cases i <;> decide)
      · exact absurd h1 (by fin_cases i <;> decide)
    have hne2 : s(x (i + 2), x (i + 3)) ≠ s(u, v) := by
      intro hsym
      rcases hsym_imp _ _ hsym with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 (by fin_cases i <;> decide)
      · exact absurd h1 (by fin_cases i <;> decide)
    refine ⟨S'.erase Q, Q, ⟨hS_pack, hQcard, hS_disj, hS_cov⟩,
      huQ, hvQ, hnadj, x (i + 1), x (i + 2), ?_, ?_, ?_, ?_⟩
    · rw [hs4 i, ← hi, ← hj]
    · rw [← hi]
      exact hG_of_ne_edge _ _ e01 hne0
    · exact hG_of_ne_edge _ _ e12 hne1
    · rw [← hj]
      exact hG_of_ne_edge _ _ e23 hne2

/-- **Packaging for an edge-maximal counterexample.**  If `G` is factor-free
but the addition of any missing edge creates a quadrilateral factor, then
any non-edge `u - v` yields a cover whose leftover carries the `P₄`
`u - a - b - v`. -/
theorem cover_exists_of_edgeMax (hG : ¬ G.HasQuadFactor)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → (addEdge G u v).HasQuadFactor)
    {u v : V} (huv : u ≠ v) (hnadj : ¬ G.Adj u v) :
    ∃ S : Finset (Finset V), ∃ U : Finset V,
      G.IsCover S U ∧ u ∈ U ∧ v ∈ U ∧ ¬ G.Adj u v ∧
        ∃ a b : V, U = {u, a, b, v} ∧ G.Adj u a ∧ G.Adj a b ∧ G.Adj b v :=
  cover_of_added_edge_factor huv hnadj (hmax u v huv hnadj) hG

end SimpleGraph
