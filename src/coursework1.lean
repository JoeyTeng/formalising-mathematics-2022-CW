/-
Copyright (c) 2015 Joey Teng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joey Teng.
-/
import tactic -- imports all the Lean tactics
import combinatorics.simple_graph.connectivity


-- Graph Theory

universe u

namespace simple_graph
variables {V : Type u} (G : simple_graph V)


/-!
## Connectivity

Utilities about `walk`, `trail` and `path`.
-/

-- def trail_from_walk [decidable_eq V]: Π {v w : V}, G.walk v w → G.walk v w
-- | _ _ walk.nil := walk.nil
-- | x _ (walk.cons p q) :=
--   if q.edges.nodup then walk.cons p q else walk.cons p q

-- def walk_drop_loop [decidable_eq V]: Π {u v w : V}, G.adj u v → G.walk u w → G.walk v w
-- | _ v w _ (walk.cons _ walk.nil) := G.walk v w
-- | u v w adj (walk.cons a t) := if

def subwalk_nil_from_vertex : Π {u : V}, G.walk u u
| u := (walk.nil : G.walk u u)

-- def walk_from_edges : Π {u v : V}, list (sym2 V) → G.walk u v
-- | u v (a :: []) := walk.cons (a : G.adj u v) (walk.nil : G.walk v v)

-- def subwalk_from_adj [decidable_eq V]:
--   Π {u v w x: V}, G.adj u v → G.walk w x → G.walk u x
-- | u _ _ x adj walk.nil := walk.cons adj (walk.nil : G.walk x x)
-- | u v w x _adj (walk.cons (adj _ _) q) :=
--   if p u v then walk.cons p q else subwalk_from_vertex u q


theorem is_trail_nil {v : V} (p : G.walk v v): p = walk.nil → p.is_trail :=
begin
  intro hp,
  rw hp,
  simp,
end


theorem has_trail_iff_walk {v w : V} (p : G.walk v w) [decidable_eq V]:
  ∃ ⦃p' : G.walk v w⦄, p'.is_trail :=
begin
  induction p with d v_ mid w_ adj walk_ hd,
  { dsimp at *,
    fsplit,
    work_on_goal 0 { refl },
    fsplit,
    exact dec_trivial,
  },
  { cases hd with trail_ h,
    -- by_cases hdup : adj ∈ trail_.edges, -- not working
    -- Should discuss by cases
    -- If adj is a dup, then roll-back all the way s.t. adj is not a dup
    -- Else append_left
    have t' := walk.cons adj trail_,
    have htcons : t' = walk.cons adj trail_,
    {
      sorry,
    },
    have ht' : t'.is_trail,
    {
      sorry,
      -- rw t',
      -- rw walk.cons_is_trail_iff,
    },
    use t',
    exact ht'
  },
end

/-!
## Reachable

Based on `simple_graph.walk`
-/

/-- Exists an walk in `G` from `v` to `w` --/
def reachable (v w : V) : Prop :=
  ∃ p : G.walk v w, true

theorem reachable_def {v w : V} :
  G.reachable v w ↔ ∃ ⦃p : G.walk v w⦄, true :=
begin
  refl,
end

theorem reachable_if_walk {v w : V} (p : G.walk v w):
  G.reachable v w :=
begin
  use p,
end

/-- `v` is always reachable to itself --/
@[simp]
theorem reachable_self {v : V} : G.reachable v v :=
begin
  use walk.nil,
end

@[simp]
theorem reachable_trans {u v w : V} :
  G.reachable u v → G.reachable v w → G.reachable u w :=
begin
  intros h1 h2,
  cases h1 with p1 hp1,
  cases h2 with p2 hp2,
  have p := p1.append p2,
  use p,
end

-- @[simp]
theorem reachable_symm {u v : V} :
  G.reachable u v → G.reachable v u :=
begin
  intro h,
  cases h with p _,
  use p.reverse,
end

@[simp]
theorem reachable_adj {v w : V} : G.adj v w → G.reachable v w :=
begin
  intro h,
  have p : G.walk v w,
  { constructor,
    assumption,
    exact walk.nil, },
  use p,
end

theorem reachable_if_passing {u v w : V} (p : G.walk u w):
  v ∈ p.support → G.reachable v w :=
begin
  intro hp,
  fconstructor,
  {
    haveI support := p.support,
    sorry,
  },
  { triv },
end

theorem reachable_if_support {u v w x : V} :
  ∃ {p : G.walk u x}, v ∈ p.support ∧ w ∈ p.support → G.reachable v w :=
begin
  sorry,
end

/-### Extend to trail-/

theorem reachable_trail {v w : V} :
  G.reachable v w ↔ ∃ ⦃p : G.walk v w⦄, p.is_trail :=
begin
  split,
  { simp,
    intro h,
    rw reachable at h,
    cases h with p _,
    use p,
    sorry,
  },
  { simp,
    intros x hx,
    use x,
  },
end

/-!## Connected-/

/-- All vertices are reachable to each other --/
def is_connected : Prop :=
  ∀ ⦃v w : V⦄, G.reachable v w

/-- Complete Graph is connected.
  Note that empty graph may not, unless `V` is empty. --/
theorem complete_graph_is_connected : G = ⊤ → G.is_connected :=
begin
  intros hG v w,
  by_cases eq : v = w,
  { rw eq,
    exact G.reachable_self, },
  { rw ← ne at eq,
    have p : G.walk v w,
    {
       have h : G.adj v w,
      { finish, },
      { exact walk.cons h walk.nil },
    },
    rw reachable,
    use p,
  },
end

/-!## Eulerian Walks-/
section Eulerian
variables [decidable_eq V]

def is_euler_circuit {v : V} (p : G.walk v v) : Prop :=
  p.is_circuit ∧ ∀ ⦃e : sym2 V⦄, e ∈ G.edge_set → (e ∈ p.edges)

def is_eulerian [decidable_eq V] : Prop :=
  ∃ {v : V}, ∃ {p : G.walk v v}, G.is_euler_circuit p

theorem eulerian_is_connected :
  G.is_eulerian → G.is_connected :=
begin
  rw is_eulerian,
  intro h,
  cases h with v hv,
  cases hv with p hp,
  sorry,
end

theorem eulerian_all_even_degree [decidable_rel G.adj] [fintype V] :
  G.is_eulerian → ∀ (v : V), even (G.degree v):=
begin
  sorry
end

/-Euler's Theorem-/
theorem is_eulerian_iff_all_even_degree [decidable_rel G.adj] [fintype V] :
  is_connected G ∧ ∀ (v : V), even (G.degree v) ↔ G.is_eulerian :=
begin
  sorry
end


/-!### Example: Seven Bridges of Königsberg

  A modified version of "Seven Bridges of Königsberg", which now contains a Euler path.

  Two duplicated edges (bridges) are removed from the original graph.
-/
section Konigsberg

/- Four sectors -/
@[derive decidable_eq]
inductive sector_
| v1 : sector_
| v2 : sector_
| v3 : sector_
| v4 : sector_

/-
  v1
  | \
  v2 - v4
  | /
  v3
-/
def bridge_ : sector_ → sector_ → Prop
| sector_.v1 sector_.v3 := false
| sector_.v3 sector_.v1 := false
| _ _ := true

/-
  A Euler Graph

    v1
   / \
  v2  v4
   \ /
    v3
-/
def bridge_2 : sector_ → sector_ → Prop
| sector_.v1 sector_.v3 := false
| sector_.v3 sector_.v1 := false
| sector_.v2 sector_.v4 := false
| sector_.v4 sector_.v2 := false
| _ _ := true

def graph_ : simple_graph sector_ := simple_graph.from_rel bridge_
def graph_2 : simple_graph sector_ := simple_graph.from_rel bridge_2

example : sector_.v1 ≠ sector_.v4 :=
begin
  exact dec_trivial
end

example {G : simple_graph sector_}:
   G = graph_2 → G.is_eulerian :=
begin
  intro h,
  have v1 := sector_.v1,
  have v2 := sector_.v2,
  have v3 := sector_.v3,
  have v4 := sector_.v4,
  rw is_eulerian,
  use v4,
  have p' : G.walk v4 v4 := walk.nil,
  have e14 : G.adj v1 v4,
  { rw h,
    split,
    { sorry, },
    { have h_ := bridge_2(v1)(v4),
      sorry,
    },
  },
  have e21 : G.adj v2 v1,
  { sorry, }, -- same as e14
  have e32 : G.adj v3 v2,
  { sorry, },
  have e43 : G.adj v4 v3,
  { sorry, },
  have p : G.walk v4 v4 := walk.cons e43 (walk.cons e32 (walk.cons e21 (walk.cons e14 p'))),
  use p,
  rw is_euler_circuit,
  split,
  {
    split,
    {
      split,
      rw list.nodup,
      sorry,
    },
    {
      intro h,
      sorry, -- by the construction of p
    },
  },
  intro e,
  intro he,
  have _set := G.edge_set,
  induction e,
  { cases e,
    sorry,
  },
  { refl },
end

end Konigsberg

end Eulerian

end simple_graph
