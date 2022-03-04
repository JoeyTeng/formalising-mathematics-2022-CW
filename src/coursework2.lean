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
## Suppliments / Refinement to Connectivity

-/
namespace walk
variables {G} [decidable_eq V]

lemma support_drop_until_in {v w : V} (p : G.walk v w) (u : V) (h : u ∈ p.support): u ∈ (p.drop_until u h).support :=
begin
  finish,
end

lemma support_bypass_subset' {u v : V} (p : G.walk u v) : p.support ⊆
 p.bypass.support :=
begin
  induction p,
  { simp!, },
  { simp! only,
    split_ifs,
    {
      have h : p_p.bypass.support ⊆ p_p.support,
      { exact support_bypass_subset p_p, },
      by_cases hcases : p_u ∈ p_p.support,
      {
        intros v' h'',
        cases h'',
        { finish, },
        {
          sorry,
        },
      },
      { tauto, },
    },
    { rw support_cons,
      apply list.cons_subset_cons,
      assumption, }, },
end

end walk


/-!
## Connectivity

Utilities about `walk`, `trail` and `path`.
-/

def subwalk_nil_from_vertex : Π {u : V}, G.walk u u
| u := (walk.nil : G.walk u u)

theorem is_trail_nil {v : V} (p : G.walk v v): p = walk.nil → p.is_trail :=
begin
  intro hp,
  rw hp,
  simp,
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

@[simp]
theorem reachable_symm {u v : V} :
  G.reachable u v ↔ G.reachable v u :=
begin
  split;
  intro h;
  cases h with p _;
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

theorem reachable_if_passing {u v w : V} (p : G.walk u w) (hp : v ∈ p.support) [decidable_eq V]:
  G.reachable v w :=
begin
  rw reachable_def,
  fconstructor,
  {
    let p' : G.walk u w := p.to_path,
    have hp' : v ∈ p'.support,
    {
      apply walk.support_bypass_subset',
      exact hp,
    },
    have hp'' : p'.is_path,
    { exact walk.bypass_is_path p, },
    let q : G.walk v w := p'.drop_until v hp',
    use q,
  },
  { triv },
end

theorem reachable_if_support {u v w x : V} (p : G.walk u x) (h1 : v ∈ p.support) (h2 : w ∈ p.support) [decidable_eq V]:
  G.reachable v w :=
begin
  have h' : G.reachable v x,
  { apply reachable_if_passing G p h1, },
  have h'' : G.reachable w x,
  { apply reachable_if_passing G p h2, },
  have h''' : G.reachable x w,
  {
    rw G.reachable_symm at h'',
    exact h'',
  },

  -- Unsure how to use "reachable_trans", thus copy over
  cases h' with p1 hp1,
  cases h''' with p2 hp2,
  have p := p1.append p2,
  use p,
end

/-### Extend to path-/

theorem reachable_path {v w : V} [decidable_eq V]:
  G.reachable v w ↔ ∃ ⦃p : G.walk v w⦄, p.is_path :=
begin
  split,
  { simp,
    intro h,
    rw reachable at h,
    cases h with p _,
    let p' : G.walk v w := p.bypass,
    use p',
    exact walk.bypass_is_path p,
  },
  { simp,
    intros x hx,
    use x,
  },
end

/-### Extend to trail-/

theorem reachable_trail {v w : V} [decidable_eq V]:
  G.reachable v w ↔ ∃ ⦃p : G.walk v w⦄, p.is_trail :=
begin
  split,
  { rw reachable_path,
    intro h,
    cases h with p hp,
    use p,
    let p' := hp.to_trail,
    exact p',
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
  p.is_circuit ∧ (∀ ⦃e : sym2 V⦄, e ∈ G.edge_set → (e ∈ p.edges)) ∧ ∀ ⦃u : V⦄, u ∈ p.support

def is_eulerian [decidable_eq V] : Prop :=
  ∃ {v : V}, ∃ {p : G.walk v v}, G.is_euler_circuit p

theorem eulerian_is_connected :
  G.is_eulerian → G.is_connected :=
begin
  rw is_eulerian,
  intro h,
  cases h with u hu,
  cases hu with p hp,
  rw is_euler_circuit at hp,
  obtain ⟨hp, he, hV⟩ := hp,
  rw is_connected,
  intros v w,
  have hv : v ∈ p.support,
  { tauto, },
  have hw : w ∈ p.support,
  { tauto, },
  exact G.reachable_if_support p hv hw,
end

theorem eulerian_all_even_degree [decidable_rel G.adj] [fintype V] :
  G.is_eulerian → ∀ (v : V), even (G.degree v):=
begin
  intro h,
  cases h with u hu,
  cases hu with p hp,
  obtain ⟨hp, he, hV⟩ := hp,

  intro v,
  have hv : v ∈ p.support,
  { apply hV, },
  let pe := p.edges,
  let deg := G.degree v,
  have hdeg : even deg,
  {
    -- Either
    -- - v == u, thus list's first sym2 has a v, and last sym2 has a v
    -- - v != u, thus
      -- for each (sym2 V), i-th element is (_, v) → i+1-th element is (v, __)
      -- hence (sym2 V) comes in pairs
      -- thus degree is even.
    sorry,
  },
  exact hdeg,
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

example {G : simple_graph sector_} [decidable_rel G.adj] [fintype sector_]:
   G = graph_2 → G.is_eulerian :=
begin
  intro h,
  -- construct such a circuit
  let v1 := sector_.v1,
  let v2 := sector_.v2,
  let v3 := sector_.v3,
  let v4 := sector_.v4,
  rw is_eulerian,
  use v4,
  let p' : G.walk v4 v4 := walk.nil,
  have e14 : G.adj v1 v4,
  {
    rw h,
    fconstructor;
    tauto,
  },
  have e21 : G.adj v2 v1,
  {
    rw h,
    fconstructor;
    tauto,
  }, -- same as e14
  have e32 : G.adj v3 v2,
  {
    rw h,
    fconstructor;
    tauto,
  },
  have e43 : G.adj v4 v3,
  {
    rw h,
    fconstructor;
    tauto,
  },
  let p : G.walk v4 v4 := walk.cons e43 (walk.cons e32 (walk.cons e21 (walk.cons e14 p'))),
  -- END of circuit construction
  use p,
  rw is_euler_circuit,
  split,
  {
    fconstructor,
    {
      fconstructor,
      exact dec_trivial,
    },
    { exact dec_trivial, },
  },
  split,
  -- prove edges
  {
    intro e,
    intro he,
    let _set := G.edge_set,
    rw ← mem_edge_set at *,
    have h_set : _set = G.edge_set,
    { refl, },
    have hset : graph_2.edge_set = {⟦(v1, v4)⟧, ⟦(v2, v1)⟧, ⟦(v3, v2)⟧, ⟦(v4, v3)⟧},
    {
      sorry,
    },
    rw ← h at hset,
    rw hset at h_set,
    norm_num,
    by_cases hc : e = ⟦(v4, v3)⟧,
    { left, exact hc, },
    {
      by_cases hc' : e = ⟦(v3, v2)⟧,
      { right, left, exact hc', },
      {
        by_cases hc'' : e = ⟦(v2, v1)⟧,
        { right, right, left, exact hc'', },
        {
          by_cases hc''' : e = ⟦(v1, v4)⟧,
          { right, right, right, exact hc''', },
          { finish, },
        },
      },
    },
  },
  -- proving vertices
  {
    intro u,
    norm_num,
    cases u,
    {
      right, right, right, left,
      refl,
    },
    {
      right, right, left,
      refl,
    },
    {
      right, left,
      refl,
    },
    {
      left,
      refl,
    },
  },
end

end Konigsberg

end Eulerian

end simple_graph
