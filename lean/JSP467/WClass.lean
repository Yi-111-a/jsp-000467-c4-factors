import JSP467.WDefs
import JSP467.Chord

/-!
# JSP-000467 — finite classification of dense 4-vertex sets

Wang's switching arguments repeatedly use the following elementary
classification: a simple graph on four vertices with at least four edges
either contains a quadrilateral `C₄` or contains a triangle.  Indeed, the
complement then has at most two edges; if the missing edges are disjoint the
four remaining edges form `C₄`, and if they share a vertex the other three
vertices form a triangle (the graph is a *paw*, or denser).

* `IsTriangle.of_three` / `exists_triangle_of_three` — triangle constructors.
* `edgeSum_quad` — the internal edge-sum of a 4-set is twice the sum of the
  six adjacency indicators.
* `quad_or_triangle_of_dense` — the classification theorem.
* `exists_triangle_of_dense_not_quad` and
  `edgeSum_le_six_of_quadfree_trianglefree` — the contrapositive
  formulations used downstream.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Triangle constructor: three distinct pairwise-adjacent vertices form a
triangle. -/
theorem IsTriangle.of_three {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (e1 : G.Adj x y) (e2 : G.Adj x z) (e3 : G.Adj y z) :
    G.IsTriangle {x, y, z} := by
  refine ⟨?_, ?_⟩
  · simp [hxy, hxz, hyz]
  · intro p hp q hq hpq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
    · exact absurd rfl hpq
    · exact e1
    · exact e2
    · exact e1.symm
    · exact absurd rfl hpq
    · exact e3
    · exact e2.symm
    · exact e3.symm
    · exact absurd rfl hpq

omit [Fintype V] [DecidableRel G.Adj] in
/-- Packaged triangle existence: three pairwise-adjacent distinct vertices
of `U` yield a triangle `T ⊆ U`. -/
theorem exists_triangle_of_three {U : Finset V} {x y z : V}
    (hx : x ∈ U) (hy : y ∈ U) (hz : z ∈ U) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (e1 : G.Adj x y) (e2 : G.Adj x z) (e3 : G.Adj y z) :
    ∃ T ⊆ U, G.IsTriangle T :=
  ⟨{x, y, z},
    by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption,
    IsTriangle.of_three hxy hxz hyz e1 e2 e3⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- An adjacency indicator contributes at most `1`. -/
theorem ite_le_one (P : Prop) [Decidable P] :
    (if P then (1 : ℕ) else 0) ≤ 1 := by
  by_cases h : P <;> simp [h]

/-- The number of neighbours of `u` inside `{u, x, y, z}` equals the sum of
the three adjacency indicators `u ~ x`, `u ~ y`, `u ~ z` (the vertex `u`
itself never contributes, whether or not it is distinct). -/
theorem card_quad_self_neighbor (u x y z : V) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) :
    (({u, x, y, z} : Finset V) ∩ G.neighborFinset u).card =
      (if G.Adj u x then 1 else 0) + (if G.Adj u y then 1 else 0) +
        (if G.Adj u z then 1 else 0) := by
  have hu : u ∉ G.neighborFinset u := fun h =>
    absurd rfl (G.ne_of_adj ((G.mem_neighborFinset u u).1 h))
  rw [Finset.insert_inter_of_notMem hu]
  have f : ({x, y, z} : Finset V) ∩ G.neighborFinset u
      = ({x, y, z} : Finset V).filter (G.Adj u) := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_filter, G.mem_neighborFinset]
  rw [f, Finset.card_filter,
    Finset.sum_insert (by simp [hxy, hxz]),
    Finset.sum_insert (by simp [hyz]),
    Finset.sum_singleton]
  omega

/-- Twice the edge count inside a 4-set: `edgeSum {a,b,c,d}` equals twice
the sum of the six adjacency indicators. -/
theorem edgeSum_quad (a b c d : V) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    edgeSum G {a, b, c, d} =
      2 * ((if G.Adj a b then 1 else 0) + (if G.Adj a c then 1 else 0) +
        (if G.Adj a d then 1 else 0) + (if G.Adj b c then 1 else 0) +
        (if G.Adj b d then 1 else 0) + (if G.Adj c d then 1 else 0)) := by
  unfold edgeSum
  rw [Finset.sum_insert (by simp [hab, hac, had]),
    Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_insert (by simp [hcd]),
    Finset.sum_singleton]
  rw [card_quad_self_neighbor a b c d hbc hbd hcd]
  have eB : ({a, b, c, d} : Finset V) ∩ G.neighborFinset b
      = {b, a, c, d} ∩ G.neighborFinset b := by
    congr 1
    exact Finset.insert_comm a b {c, d}
  have eC : ({a, b, c, d} : Finset V) ∩ G.neighborFinset c
      = {c, a, b, d} ∩ G.neighborFinset c := by
    congr 1
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have eD : ({a, b, c, d} : Finset V) ∩ G.neighborFinset d
      = {d, a, b, c} ∩ G.neighborFinset d := by
    congr 1
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [eB, card_quad_self_neighbor b a c d hac had hcd]
  rw [eC, card_quad_self_neighbor c a b d hab had hbd]
  rw [eD, card_quad_self_neighbor d a b c hab hac hbc]
  rw [if_congr (G.adj_comm b a) rfl rfl,
    if_congr (G.adj_comm c a) rfl rfl,
    if_congr (G.adj_comm c b) rfl rfl,
    if_congr (G.adj_comm d a) rfl rfl,
    if_congr (G.adj_comm d b) rfl rfl,
    if_congr (G.adj_comm d c) rfl rfl]
  omega

/-- **Classification of dense 4-vertex sets.**  A 4-vertex induced subgraph
with at least four edges (`edgeSum ≥ 8`) either is a quadrilateral block
(contains `C₄`) or contains a triangle. -/
theorem quad_or_triangle_of_dense {U : Finset V} (hcard : U.card = 4)
    (h8 : 8 ≤ edgeSum G U) :
    G.IsQuadBlock U ∨ ∃ T ⊆ U, G.IsTriangle T := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hU⟩ :=
    Finset.card_eq_four.1 hcard
  subst hU
  have hE := edgeSum_quad (G := G) a b c d hab hac had hbc hbd hcd
  rw [hE] at h8
  have haU : a ∈ ({a, b, c, d} : Finset V) := Finset.mem_insert_self a _
  have hbU : b ∈ ({a, b, c, d} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self b _)
  have hcU : c ∈ ({a, b, c, d} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_self c _))
  have hdU : d ∈ ({a, b, c, d} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self d)))
  have hU2 : ({a, b, c, d} : Finset V) = {a, c, b, d} := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hU3 : ({a, b, c, d} : Finset V) = {a, b, d, c} := by
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  -- Case analysis on the six pairs `{a,b}, {a,c}, {a,d}, {b,c}, {b,d}, {c,d}`.
  -- At most two of them may be non-edges (three non-edges force
  -- `edgeSum ≤ 6`, contradicting `h8`).  Two non-edges sharing a vertex
  -- leave a triangle on the other three vertices; disjoint non-edges (or
  -- fewer) leave a `C₄`.
  by_cases hab' : G.Adj a b
  · by_cases hac' : G.Adj a c
    · by_cases had' : G.Adj a d
      · -- `a` sees all of `b, c, d`; any edge among them gives a triangle.
        by_cases hbc' : G.Adj b c
        · exact Or.inr (exists_triangle_of_three haU hbU hcU hab hac hbc
            hab' hac' hbc')
        · by_cases hbd' : G.Adj b d
          · exact Or.inr (exists_triangle_of_three haU hbU hdU hab had hbd
              hab' had' hbd')
          · by_cases hcd' : G.Adj c d
            · exact Or.inr (exists_triangle_of_three haU hcU hdU hac had hcd
                hac' had' hcd')
            · exfalso
              simp [hab', hac', had', hbc', hbd', hcd'] at h8
      · -- `a` misses only `d`.
        by_cases hbd' : G.Adj b d
        · by_cases hcd' : G.Adj c d
          · -- cycle `a - b - d - c - a`
            exact Or.inl (IsQuadBlock.of_cycle hU3 hab had hac hbd hbc
              hcd.symm hab' hbd' hcd'.symm hac'.symm)
          · by_cases hbc' : G.Adj b c
            · exact Or.inr (exists_triangle_of_three haU hbU hcU hab hac hbc
                hab' hac' hbc')
            · exfalso
              simp [hab', hac', had', hbc', hbd', hcd'] at h8
        · by_cases hbc' : G.Adj b c
          · exact Or.inr (exists_triangle_of_three haU hbU hcU hab hac hbc
              hab' hac' hbc')
          · exfalso
            simp [hab', hac', had', hbc', hbd'] at h8
            have e1 := ite_le_one (G.Adj c d)
            omega
    · by_cases had' : G.Adj a d
      · -- `a` misses only `c`.
        by_cases hbc' : G.Adj b c
        · by_cases hcd' : G.Adj c d
          · -- cycle `a - b - c - d - a`
            exact Or.inl (IsQuadBlock.of_cycle rfl hab hac had hbc hbd hcd
              hab' hbc' hcd' had'.symm)
          · by_cases hbd' : G.Adj b d
            · exact Or.inr (exists_triangle_of_three haU hbU hdU hab had hbd
                hab' had' hbd')
            · exfalso
              simp [hab', hac', had', hbc', hbd', hcd'] at h8
        · by_cases hbd' : G.Adj b d
          · exact Or.inr (exists_triangle_of_three haU hbU hdU hab had hbd
              hab' had' hbd')
          · exfalso
            simp [hab', hac', had', hbc', hbd'] at h8
            have e1 := ite_le_one (G.Adj c d)
            omega
      · -- `a` misses `c` and `d`: `{b, c, d}` is forced to be a triangle.
        by_cases hbc' : G.Adj b c
        · by_cases hbd' : G.Adj b d
          · by_cases hcd' : G.Adj c d
            · exact Or.inr (exists_triangle_of_three hbU hcU hdU hbc hbd hcd
                hbc' hbd' hcd')
            · exfalso
              simp [hab', hac', had', hbc', hbd', hcd'] at h8
          · exfalso
            simp [hab', hac', had', hbc', hbd'] at h8
            have e1 := ite_le_one (G.Adj c d)
            omega
        · exfalso
          simp [hab', hac', had', hbc'] at h8
          have e1 := ite_le_one (G.Adj b d)
          have e2 := ite_le_one (G.Adj c d)
          omega
  · by_cases hac' : G.Adj a c
    · by_cases had' : G.Adj a d
      · -- `a` misses only `b`.
        by_cases hbc' : G.Adj b c
        · by_cases hbd' : G.Adj b d
          · -- cycle `a - c - b - d - a`
            exact Or.inl (IsQuadBlock.of_cycle hU2 hac hab had hbc.symm hcd
              hbd hac' hbc'.symm hbd' had'.symm)
          · by_cases hcd' : G.Adj c d
            · exact Or.inr (exists_triangle_of_three haU hcU hdU hac had hcd
                hac' had' hcd')
            · exfalso
              simp [hab', hac', had', hbc', hbd', hcd'] at h8
        · by_cases hbd' : G.Adj b d
          · by_cases hcd' : G.Adj c d
            · exact Or.inr (exists_triangle_of_three haU hcU hdU hac had hcd
                hac' had' hcd')
            · exfalso
              simp [hab', hac', had', hbc', hbd', hcd'] at h8
          · exfalso
            simp [hab', hac', had', hbc', hbd'] at h8
            have e1 := ite_le_one (G.Adj c d)
            omega
      · -- `a` misses `b` and `d`: `{b, c, d}` is forced to be a triangle.
        by_cases hbc' : G.Adj b c
        · by_cases hbd' : G.Adj b d
          · by_cases hcd' : G.Adj c d
            · exact Or.inr (exists_triangle_of_three hbU hcU hdU hbc hbd hcd
                hbc' hbd' hcd')
            · exfalso
              simp [hab', hac', had', hbc', hbd', hcd'] at h8
          · exfalso
            simp [hab', hac', had', hbc', hbd'] at h8
            have e1 := ite_le_one (G.Adj c d)
            omega
        · exfalso
          simp [hab', hac', had', hbc'] at h8
          have e1 := ite_le_one (G.Adj b d)
          have e2 := ite_le_one (G.Adj c d)
          omega
    · -- `a` misses `b` and `c`: `{b, c, d}` is forced to be a triangle.
      by_cases had' : G.Adj a d
      · by_cases hbc' : G.Adj b c
        · by_cases hbd' : G.Adj b d
          · by_cases hcd' : G.Adj c d
            · exact Or.inr (exists_triangle_of_three hbU hcU hdU hbc hbd hcd
                hbc' hbd' hcd')
            · exfalso
              simp [hab', hac', had', hbc', hbd', hcd'] at h8
          · exfalso
            simp [hab', hac', had', hbc', hbd'] at h8
            have e1 := ite_le_one (G.Adj c d)
            omega
        · exfalso
          simp [hab', hac', had', hbc'] at h8
          have e1 := ite_le_one (G.Adj b d)
          have e2 := ite_le_one (G.Adj c d)
          omega
      · exfalso
        simp [hab', hac', had'] at h8
        have e1 := ite_le_one (G.Adj b c)
        have e2 := ite_le_one (G.Adj b d)
        have e3 := ite_le_one (G.Adj c d)
        omega

/-- A dense 4-set that is not a quad block must contain a triangle. -/
theorem exists_triangle_of_dense_not_quad {U : Finset V} (hcard : U.card = 4)
    (h8 : 8 ≤ edgeSum G U) (hnot : ¬ G.IsQuadBlock U) :
    ∃ T ⊆ U, G.IsTriangle T :=
  (quad_or_triangle_of_dense hcard h8).resolve_left hnot

/-- Contrapositive: a 4-set carrying neither `C₄` nor a triangle has at most
three internal edges (`edgeSum ≤ 6`). -/
theorem edgeSum_le_six_of_quadfree_trianglefree {U : Finset V}
    (hcard : U.card = 4) (hq : ¬ G.IsQuadBlock U)
    (ht : ¬ ∃ T ⊆ U, G.IsTriangle T) :
    edgeSum G U ≤ 6 := by
  by_cases h8 : 8 ≤ edgeSum G U
  · rcases quad_or_triangle_of_dense hcard h8 with hQ | hT
    · exact absurd hQ hq
    · exact absurd hT ht
  · obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hU⟩ :=
      Finset.card_eq_four.1 hcard
    subst hU
    rw [edgeSum_quad a b c d hab hac had hbc hbd hcd] at h8 ⊢
    omega

omit [Fintype V] [DecidableRel G.Adj] in
/-- A vertex `u` adjacent to all of `x, y, z` inside `{u, x, y, z}`, together
with any edge among `x, y, z`, yields a triangle inside the 4-set. -/
theorem exists_triangle_of_universal_vertex {u x y z : V}
    (hux : G.Adj u x) (huy : G.Adj u y) (huz : G.Adj u z)
    (hedge : G.Adj x y ∨ G.Adj x z ∨ G.Adj y z) :
    ∃ T ⊆ ({u, x, y, z} : Finset V), G.IsTriangle T := by
  have hu : u ∈ ({u, x, y, z} : Finset V) := Finset.mem_insert_self u _
  have hx : x ∈ ({u, x, y, z} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self x _)
  have hy : y ∈ ({u, x, y, z} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_self y _))
  have hz : z ∈ ({u, x, y, z} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self z)))
  rcases hedge with h | h | h
  · exact exists_triangle_of_three hu hx hy (G.ne_of_adj hux)
      (G.ne_of_adj huy) (G.ne_of_adj h) hux huy h
  · exact exists_triangle_of_three hu hx hz (G.ne_of_adj hux)
      (G.ne_of_adj huz) (G.ne_of_adj h) hux huz h
  · exact exists_triangle_of_three hu hy hz (G.ne_of_adj huy)
      (G.ne_of_adj huz) (G.ne_of_adj h) huy huz h

/-- If `u` has at least three neighbours inside `{u, x, y, z}` (with `x, y, z`
distinct), then `u` is adjacent to all three of them. -/
theorem adj_all_of_three_neighbors {u x y z : V} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z)
    (h : 3 ≤ (({u, x, y, z} : Finset V) ∩ G.neighborFinset u).card) :
    G.Adj u x ∧ G.Adj u y ∧ G.Adj u z := by
  rw [card_quad_self_neighbor u x y z hxy hxz hyz] at h
  have e1 := ite_le_one (G.Adj u x)
  have e2 := ite_le_one (G.Adj u y)
  have e3 := ite_le_one (G.Adj u z)
  refine ⟨?_, ?_, ?_⟩ <;> by_contra hc <;> simp_all <;> omega

end SimpleGraph
