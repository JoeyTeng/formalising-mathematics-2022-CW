/-
Copyright (c) 2022 Joey Teng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joey Teng.
-/
import tactic -- imports all the Lean tactics
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.degree_sum
import combinatorics.simple_graph.subgraph
import data.fintype.basic
import data.fin_enum


-- Graph Theory

universe u

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

/-!
## Reachable

Based on `simple_graph.walk`
-/

theorem reachable_from_walk {u v : V} (p : G.walk u v)[decidable_eq V]:
  G.reachable u v := by use p

theorem reachable_if_passing {u v w : V} (p : G.walk u w) (hp : v ∈ p.support) [decidable_eq V]:
  G.reachable v w := by use p.drop_until v hp

theorem reachable_if_support {u v w x : V} (p : G.walk u x) (h1 : v ∈ p.support) (h2 : w ∈ p.support) [decidable_eq V]:
  G.reachable v w :=
begin
  have h' : G.reachable v x,
  { apply reachable_if_passing G p h1, },
  have h'' : G.reachable w x,
  { apply reachable_if_passing G p h2, },
  have h''' : G.reachable x w,
  { exact simple_graph.reachable.symm (h''), },

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

/-- Non-empty Complete Graph is connected. --/
theorem complete_graph_is_connected : nonempty V ∧ G = ⊤ → G.connected :=
begin
  intro hG,
  fconstructor,
  intros v w,
  by_cases eq : v = w,
  { rw eq, },
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
  exact hG.left,
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

def subgraph.from_walk {u v : V} [decidable_rel G.adj] (p : G.walk u v): subgraph G :=
  {
    verts := {w : V | w ∈ p.support},
    adj := λ w x, ⟦(w, x)⟧ ∈ p.edges,
    adj_sub :=
    begin
      intro w,
      intro x,
      apply walk.edges_subset_edge_set p,
    end,
    edge_vert :=
    begin
      intro w,
      intro x,
      norm_num,
      exact walk.mem_support_of_mem_edges p,
    end,
    symm :=
    begin
      intro u,
      intro v,
      norm_num,
      rw sym2.eq_swap,
      norm_num,
    end,
  }

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
@[derive [decidable_eq, fintype]] -- both necessary
inductive sector_
| v1 : sector_
| v2 : sector_
| v3 : sector_
| v4 : sector_

/-
instance : fin_enum sector_ := -- not necessary
  fin_enum.of_list [sector_.v1, sector_.v2, sector_.v3, sector_.v4] (λ x, by cases x; simp)
-/

/-
  v1
  | \
  v2 - v4
  | /
  v3
-/
@[derive decidable_rel]
def bridge_ (a b : sector_) : Prop :=
  a ≠ b ∧
  ¬ ((a = sector_.v1 ∧ b = sector_.v3) ∨ (a = sector_.v3 ∧ b = sector_.v1))

/-
  A Euler Graph

    v1
   / \
  v2  v4
   \ /
    v3
-/
@[derive decidable_rel]
def bridge_2 (a b : sector_) : Prop :=
/- (a = sector_.v1 ∧ b = sector_.v2) ∨ -/ (a = sector_.v2 ∧ b = sector_.v1) ∨
/- (a = sector_.v2 ∧ b = sector_.v3) ∨ -/ (a = sector_.v3 ∧ b = sector_.v2) ∨
/- (a = sector_.v3 ∧ b = sector_.v4) ∨ -/ (a = sector_.v4 ∧ b = sector_.v3) ∨
/- (a = sector_.v4 ∧ b = sector_.v1) ∨ -/ (a = sector_.v1 ∧ b = sector_.v4)


def graph_ : simple_graph sector_ := simple_graph.from_rel bridge_
-- @[derive decidable] -- not necessary
def graph_2 : simple_graph sector_ := simple_graph.from_rel bridge_2


theorem mem_edge_set_adj {pair : prod V V} : ⟦pair⟧ ∈ G.edge_set ↔ G.adj pair.fst pair.snd :=
begin
  split,
  { exact (mem_edge_set G).mp, },
  { exact (mem_edge_set G).mpr, },
end

example : graph_2.is_eulerian :=
begin
  -- construct such a circuit
  let v1 := sector_.v1,
  let v2 := sector_.v2,
  let v3 := sector_.v3,
  let v4 := sector_.v4,
  have v1_eq : v1 = sector_.v1 := by refl,
  have v2_eq : v2 = sector_.v2 := by refl,
  have v3_eq : v3 = sector_.v3 := by refl,
  have v4_eq : v4 = sector_.v4 := by refl,
  rw is_eulerian,
  use v4,
  let p' : graph_2.walk v4 v4 := walk.nil,
  have e14 : graph_2.adj v1 v4,
  {
    fconstructor;
    { exact dec_trivial, },
  },
  have e21 : graph_2.adj v2 v1,
  {
    fconstructor;
    { exact dec_trivial, },

  }, -- same as e14
  have e32 : graph_2.adj v3 v2,
  {
    fconstructor;
    { exact dec_trivial, },

  },
  have e43 : graph_2.adj v4 v3,
  {
    fconstructor;
    { exact dec_trivial, },
  },
  let p : graph_2.walk v4 v4 := walk.cons e43 (walk.cons e32 (walk.cons e21 (walk.cons e14 p'))),
  -- END of circuit construction
  use p,
  rw is_euler_circuit,
  split,
  -- prove p.is_circuit -- trivial
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
    intros e,
    apply quotient.induction_on e,
    clear e,

    intro a',
    rw mem_edge_set_adj,
    revert a',
    rw prod.forall,
    intros a b,
    have tmp_rw_a : (a, b).fst = a, by exact rfl,
    have tmp_rw_b : (a, b).snd = b, by exact rfl,
    rw tmp_rw_a,
    rw tmp_rw_b,
    clear tmp_rw_a tmp_rw_b,
    unfold walk.edges,
    intro hadj,
    rw list.mem_map,
    let d : graph_2.dart := {to_prod := (a, b), is_adj := hadj},
    by_cases hd : d ∈ p.darts,
    {
      use d,
      split,
      { exact hd, },
      { refl, },
    },
    {
      let d' : graph_2.dart := {to_prod := (b, a), is_adj := hadj.symm},
      have hd' : d' ∈ p.darts,
      {
        norm_num,
        norm_num at hd,
        repeat { rw not_or_distrib at hd, },
        repeat { rw dart.ext_iff at hd ⊢, },
        -- dsimp at hd h_contra,
        simp at hd ⊢,

        unfold graph_2 at hadj,
        rw from_rel_adj at hadj,
        obtain ⟨neq, hadj'⟩ := hadj,
        obtain ⟨n43, n32, n21, n14⟩ := hd,
        -- obtain ⟨n34, n23, n12, n41⟩ := h_contra,
        by_cases ha : a = v1,
        {
          right, right, left,
          by_contra h_contra,
          rw [not_and_distrib, ha] at h_contra,
          norm_num at h_contra,
          have hbn1 : ¬b = v1,
          {
            rw ha at neq,
            dsimp at neq,
            rw eq_comm at neq,
            exact neq,
          },
          have hbn4 : ¬b = v4, by exact n14 ha,
          have hbn2 := h_contra,
          have hbn3 : ¬b = v3,
          {
            by_contra bv3,
            rw [ha, bv3, v1_eq, v3_eq] at hadj',
            unfold bridge_2 at hadj',
            norm_num at hadj',
          },
          -- eliminate as has checked exhaustively; similar / same block has been used 5 times.
          clear_except v1_eq v2_eq v3_eq v4_eq hbn1 hbn2 hbn3 hbn4,
          have hb : ¬ b = v1 ∧ ¬ b = v2 ∧ ¬ b = v3 ∧ ¬ b = v4, by tauto,
          rw [v1_eq, v2_eq, v3_eq, v4_eq] at hb,
          clear_except hb,
          repeat {rw ← not_or_distrib at hb, },
          let verts : finset sector_ := sector_.fintype.elems,
          have hb' : b ∈ verts, by apply sector_.fintype.complete,
          repeat { cases hb', };
          norm_num at hb,
        },
        by_cases ha2 : a = v2,
        {
          right, left,
          by_contra h_contra,
          rw [not_and_distrib, ha2] at h_contra,
          norm_num at h_contra,
          have hbn2 : ¬b = v2,
          {
            rw ha2 at neq,
            dsimp at neq,
            rw eq_comm at neq,
            exact neq,
          },
          have hbn1 : ¬b = v1, by exact n21 ha2,
          have hbn3 := h_contra,
          have hbn4 : ¬b = v4,
          {
            by_contra bv4,
            rw [ha2, bv4, v2_eq, v4_eq] at hadj',
            unfold bridge_2 at hadj',
            norm_num at hadj',
          },
          -- eliminate as has checked exhaustively; same as above
          clear_except v1_eq v2_eq v3_eq v4_eq hbn1 hbn2 hbn3 hbn4,
          have hb : ¬ b = v1 ∧ ¬ b = v2 ∧ ¬ b = v3 ∧ ¬ b = v4, by tauto,
          rw [v1_eq, v2_eq, v3_eq, v4_eq] at hb,
          clear_except hb,
          repeat {rw ← not_or_distrib at hb, },
          let verts : finset sector_ := sector_.fintype.elems,
          have hb' : b ∈ verts, by apply sector_.fintype.complete,
          repeat { cases hb', };
          norm_num at hb,
        },
        by_cases ha3 : a = v3,
        {
          left,
          by_contra h_contra,
          rw [not_and_distrib, ha3] at h_contra,
          norm_num at h_contra,
          have hbn3 : ¬b = v3,
          {
            rw ha3 at neq,
            dsimp at neq,
            rw eq_comm at neq,
            exact neq,
          },
          have hbn2 : ¬b = v2, by exact n32 ha3,
          have hbn4 := h_contra,
          have hbn1 : ¬b = v1,
          {
            by_contra bv1,
            rw [ha3, bv1, v3_eq, v1_eq] at hadj',
            unfold bridge_2 at hadj',
            norm_num at hadj',
          },
          -- eliminate as has checked exhaustively; same as above
          clear_except v1_eq v2_eq v3_eq v4_eq hbn1 hbn2 hbn3 hbn4,
          have hb : ¬ b = v1 ∧ ¬ b = v2 ∧ ¬ b = v3 ∧ ¬ b = v4, by tauto,
          rw [v1_eq, v2_eq, v3_eq, v4_eq] at hb,
          clear_except hb,
          repeat {rw ← not_or_distrib at hb, },
          let verts : finset sector_ := sector_.fintype.elems,
          have hb' : b ∈ verts, by apply sector_.fintype.complete,
          repeat { cases hb', };
          norm_num at hb,
        },
        by_cases ha4 : a = v4,
        {
          repeat { right, },
          by_contra h_contra,
          rw [not_and_distrib, ha4] at h_contra,
          norm_num at h_contra,
          have hbn4 : ¬b = v4,
          {
            rw ha4 at neq,
            dsimp at neq,
            rw eq_comm at neq,
            exact neq,
          },
          have hbn3 : ¬b = v3, by exact n43 ha4,
          have hbn1 := h_contra,
          have hbn2 : ¬b = v2,
          {
            by_contra bv2,
            rw [ha4, bv2, v4_eq, v2_eq] at hadj',
            unfold bridge_2 at hadj',
            norm_num at hadj',
          },
          -- eliminate as has checked exhaustively; same as above
          clear_except v1_eq v2_eq v3_eq v4_eq hbn1 hbn2 hbn3 hbn4,
          have hb : ¬ b = v1 ∧ ¬ b = v2 ∧ ¬ b = v3 ∧ ¬ b = v4, by tauto,
          rw [v1_eq, v2_eq, v3_eq, v4_eq] at hb,
          clear_except hb,
          repeat {rw ← not_or_distrib at hb, },
          let verts : finset sector_ := sector_.fintype.elems,
          have hb' : b ∈ verts, by apply sector_.fintype.complete,
          repeat { cases hb', };
          norm_num at hb,
        },
        {
          -- eliminate as has checked exhaustively; similar to above
          clear_except v1_eq v2_eq v3_eq v4_eq ha ha2 ha3 ha4,
          have ha : ¬ a = v1 ∧ ¬ a = v2 ∧ ¬ a = v3 ∧ ¬ a = v4, by tauto,
          rw [v1_eq, v2_eq, v3_eq, v4_eq] at ha,
          clear_except ha,
          repeat {rw ← not_or_distrib at ha, },
          let verts : finset sector_ := sector_.fintype.elems,
          have ha' : a ∈ verts, by apply sector_.fintype.complete,
          repeat { cases ha', };
          norm_num at ha,
        },
      },
      use d',
      split,
      { exact hd', },
      {
        unfold dart.edge,
        rw sym2.eq_swap,
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
