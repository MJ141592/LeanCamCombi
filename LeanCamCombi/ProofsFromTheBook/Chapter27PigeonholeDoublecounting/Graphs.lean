/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import Mathlib

/-!
# Pigeon-hole and double counting : Graphs

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler.

We refer to chapter 27: "Pigeon-hole and double counting".
In this file, we formalize the section "Graphs".


## Structure

- `max_edges_of_c4_free_Istvan_Reiman` :
      If a 4-cycle-free graph, the number of edges is upper-bounded by the following expression in the number of vertices |V|:
      ⌊(|V|/ 4)(1 + real.sqrt (4*|V| - 3))⌋

- `c4_free` :
      Defines the property of being 4-cycle-free

- `c4_free_common_neightbours` :
      In a 4-cycle-free graph,
      two vertices have at most one common neighbour.

- `double_counting_rel` :
      Is the double counting relation we use to get the first
      inequality, `first_ineq`.

- `Cauchy_Schwartz_int` :
      A version of Cauchy-Schwartz for vectors in ℤ

- `Cauchy_Schwartz_in_action` :
      We use Cauchy-Schwartz to derive a further ineqaulity

- `commonNeighbors_c4_free` :
      The converse to `c4_free_common_neightbours`.
      If any two vertices have at most one common neighbour,
      then the graph is 4-cycle-free.


-/

open Finset LinearMap SimpleGraph
open scoped ProbabilityTheory

variable {V : Type}

-- The type of vertices
-- #check simple_graph.is_acyclic --source of inspiration for `c4_free`
/-- The graph contains no 4-cycle -/
def C4Free (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (c : G.Walk v v), ¬(c.IsCycle ∧ c.length = 4)

-- Alternatives ?
-- #check subgraph
-- #check is_subgraph
variable [Fintype V]

--[decidable_eq V]
/-
We tried following mathlib conventions: stay as general as possible.
Indeed, we can define 4-cycle free infinite graphs.
The `open_locale classical` makes the need for `[decidable_eq V]`
-/
-- #check degree
/-
The degree can be formulated as `(G.neighborSet v).to_finset.card`,
and we use it as source of inspiration to define the number of
common neighbours.
-/

open scoped Classical

/-
Otherwise, we get decidability issues for `u ∈ (G.commonNeighbors v w)`,
even with `[decidable_eq V]`.
-/
noncomputable instance tec (G : SimpleGraph V) (v w : V) : Fintype ↥(G.commonNeighbors v w) := by
  by_cases q : (G.commonNeighbors v w).Nonempty
  · dsimp [Set.Nonempty] at q
    --cases q with x xprop, --fails
    --rcases q with ⟨x, xprop⟩,  --fails
    set x := Classical.choose q with xdef
    have xprop := Classical.choose_spec q
    rw [← xdef] at xprop
    /-
       We derive finiteness by building a surjection from the type
       of common neighbours to V, which requires some dummy element
       from `G.commonNeighbors v w` we can send elements of V not in
       `G.commonNeighbors v w` to. (hence the case disjunction)
       -/
    apply
      @Fintype.ofSurjective V (↥(G.commonNeighbors v w)) _ _ fun u : V =>
        if h : u ∈ G.commonNeighbors v w then (⟨u, h⟩ : ↥(G.commonNeighbors v w))
        else (⟨x, xprop⟩ : ↥(G.commonNeighbors v w))
    simp only [Function.Surjective, SetCoe.forall]
    intro y ydef
    use y
    rw [dif_pos ydef]
  · rw [Set.not_nonempty_iff_eq_empty] at q
    rw [q]
    infer_instance

-- #check finset.card_eq_two
/-- A technical lemma extracting a pair of elements from
a finset of size ≥ 2. Comapre to mathlib's `finset.card_eq_two`.
Unfortunately, `finset.two_le_card` doesn't exist.
-/
theorem pair_of_two_le_card {α : Type} {s : Finset α} (h : 2 ≤ s.card) :
    ∃ a, ∃ b, a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  have first : 0 < s.card := by linarith
  rw [Finset.card_pos] at first
  obtain ⟨fst, fst_def⟩ := first
  use fst
  have second : 0 < (s.erase fst).card := by
    have := Finset.card_erase_add_one fst_def
    rw [← this] at h
    linarith
  rw [Finset.card_pos] at second
  obtain ⟨snd, snd_def⟩ := second
  use snd
  constructor
  exact fst_def
  constructor
  apply (Finset.erase_subset fst s) snd_def
  intro con
  rw [← con] at snd_def
  apply (Finset.not_mem_erase fst s) snd_def

/-- In a 4-cycle-free graph,
two vertices have at most one common neighbour.
-/
theorem c4Free_common_neighbours (G : SimpleGraph V) (h : C4Free G) :
    ∀ v w, v ≠ w → (commonNeighbors G v w).toFinset.card ≤ 1 := by
  intro v w vnw
  -- We proceed by contradiction
  by_contra! con
  rw [Nat.lt_iff_add_one_le] at con
  norm_num at con
  -- We get 2 common neighbours, and their properties
  obtain ⟨a, ⟨b, ⟨useless1, ⟨useless2, anb⟩⟩⟩⟩ := pair_of_two_le_card con
  clear useless1 useless2
  have adef := a.prop
  --for readability
  have bdef := b.prop
  dsimp [commonNeighbors] at *
  have vna := adef.1.ne
  have wna := adef.2.ne
  have vnb := bdef.1.ne
  have wnb := bdef.2.ne
  dsimp [C4Free] at h
  -- We build a 4-cycle and use it to derive the contradiciton
  let c4 := ((((@Walk.nil V G v).cons $ G.adj_symm adef.1).cons adef.2).cons $
    G.adj_symm bdef.2).cons bdef.1
  apply h v c4
  have for_later_too : c4.length = 4 := by
    dsimp [c4]
  constructor
  swap
  exact for_later_too
  --We must show that our construction is a 4-cycle
  · rw [Walk.isCycle_def]
    constructor
    · rw [Walk.isTrail_def]
      dsimp [c4]
      dsimp [List.Nodup]
      repeat'
        rw [List.pairwise_cons]
        constructor
        intro e edef
        fin_cases edef <;>
          · rw [not_iff_not.mpr Sym2.eq_iff]
            push_neg
            constructor
            repeat'
              intro problem
              ·
                first
                |
                  · exfalso;
                    ·
                      first
                      | · exact vnb problem
                      | · exact vnb problem.symm
                      | · exact vnw problem
                      | · exact vnw problem.symm
                      | · exact vna problem
                      | · exact vna problem.symm
                      | · exact wna problem
                      | · exact wna problem.symm
                      | · exact wnb problem
                      | · exact wnb problem.symm
                      | · exact anb problem
                      | · exact anb problem.symm
                |
                  ·
                    first
                    | · exact vnb
                    | · exact vnb.symm
                    | · exact vnw
                    | · exact vnw.symm
                    | · exact vna
                    | · exact vna.symm
                    | · exact wna
                    | · exact wna.symm
                    | · exact wnb
                    | · exact wnb.symm
                    | · intro bna; rw [Subtype.coe_inj] at bna
                    | · intro bna; rw [Subtype.coe_inj] at bna ; exact anb bna.symm
                    | · intro bna; rw [Subtype.coe_inj] at problem
                    | · intro bna; rw [Subtype.coe_inj] at problem ; exact anb problem.symm
      apply List.Pairwise.nil
    constructor
    · intro con
      apply_fun Walk.length at con
      rw [Walk.length_nil] at con
      rw [for_later_too] at con
      norm_num at con
    dsimp [c4]
    dsimp [List.Nodup]
    simp +contextual [eq_comm, *, or_imp]
    aesop

/-- We define our double-counting relation:
a vertex and a pair of vertices are in relation,
is bothe vertices of the pair are incident
to the vertex.
-/
def DoubleCountingRel (G : SimpleGraph V) (u : V) (e : Sym2 V) :=
  ∀ v ∈ e, G.Adj u v

/-- A technical lemma to get an easy criterion for when
two pairs, as finsets, are equal.
-/
theorem Finset.pair_eq {α : Type} {a b c d : α} :
    ({a, b} : Finset α) = {c, d} ↔ a = c ∧ b = d ∨ a = d ∧ b = c where
  mp h := by
    rw [Finset.ext_iff] at h
    have := h a
    have := h b
    aesop
  mpr := by aesop

/-- We show that the pairs, among those that have different elements,
that are in relation with a given vertex `u` are in number
"(deg u) choose 2"

This is the first proof, which makes use of finset pairs
in the form of `finset.card_powerset_len 2`.
-/
theorem double_count_above (G : SimpleGraph V) (u : V) :
    ((Finset.bipartiteAbove (DoubleCountingRel G) {e : Sym2 V | ¬e.IsDiag}.toFinset) u).card =
      (G.degree u).choose 2 := by
  simp only [Finset.bipartiteAbove, SimpleGraph.degree, Set.toFinset_setOf]
  -- We will put the pair of the relation in bijection
  -- with pairs of neighbours of `u`
  rw [← Finset.card_powersetCard 2 (G.neighborFinset u)]
  rw [filter_filter]
  let bij (e : Sym2 V)
    (edef : e ∈ filter (fun a : Sym2 V => ¬a.IsDiag ∧ DoubleCountingRel G u a) univ) :=
    ({e.out.1, Sym2.Mem.other (Sym2.out_fst_mem e)} : Finset V)
  apply card_bij bij
  --The mapping condition
  · intro e edef
    rw [mem_filter] at edef
    simp [DoubleCountingRel] at edef
    simp only [bij]
    rw [mem_powersetCard]
    /-
       There used to be a switch to `other' ` here ...
       the issue seems to be linked to the "only" in
       line `simp only [bij]`. Compare this to the
       "Injectivity" code block
       -/
    constructor
    · intro x xdef
      rw [mem_neighborFinset]
      rw [mem_insert, mem_singleton] at xdef
      obtain rfl | rfl := xdef
      · exact edef.2 e.out.1 (Sym2.out_fst_mem e)
      · convert edef.2 (Sym2.Mem.other <| Sym2.out_fst_mem e) (Sym2.other_mem (Sym2.out_fst_mem e))
    rw [card_eq_two]
    use e.out.1
    use Sym2.Mem.other <| Sym2.out_fst_mem e
    constructor
    · intro con; apply edef.1
      rw [← Sym2.other_spec (Sym2.out_fst_mem e)]
      simp_rw [← con]
      simp
    rfl
  -- Injectivity
  · intro e r edef rdef eq
    simp [bij] at eq
    -- using "only" will lead to failure
    rw [← Sym2.other_spec' (Sym2.out_fst_mem e)]
    rw [← Sym2.other_spec' (Sym2.out_fst_mem r)]
    rw [Sym2.eq_iff]
    rw [← Finset.pair_eq]; convert Eq
  -- Surjectivity
  · intro p pdef
    rw [mem_powersetCard] at pdef
    obtain ⟨x, ⟨y, ⟨xny, xydef⟩⟩⟩ := card_eq_two.mp pdef.2
    use s(x, y)
    have :  s(x, y) ∈ filter (fun a : Sym2 V => ¬a.IsDiag ∧ DoubleCountingRel G u a) univ := by
      rw [mem_filter]
      simp only [true_and, Finset.mem_univ, Sym2.isDiag_iff_proj_eq]
      constructor
      rw [Ne] at xny
      exact xny
      simp [DoubleCountingRel]
      constructor
      repeat'
        rw [← mem_neighbor_finset]
        apply pdef.1
        rw [xydef]
        simp
    use this
    simp [bij]
    have that := Sym2.other_spec' (Sym2.out_fst_mem  s(x, y)); rw [Sym2.eq_iff] at that
    cases that
    · rw [xydef]
      congr
      exact that.1
      exact that.2
    · rw [xydef]
      rw [pair_comm]
      congr
      exact that.2
      exact that.1

--#eval (sym2.out_fst_mem ⟦(1, 2)⟧).other'
-- then what does "This is the computable version of `mem.other`" in the docstring mean ?
/-- We show that the pairs, among those that have different elements,
that are in relation with a given vertex `u` are in number
"(deg u) choose 2"

This is the second proof, which makes use of smy2 pairs
in the form of `sym2.card_image_off_diag`.
-/
theorem double_count_above' (G : SimpleGraph V) (u : V) :
    ((Finset.bipartiteAbove (DoubleCountingRel G) {e : Sym2 V | ¬e.IsDiag}.toFinset) u).card =
      (G.degree u).choose 2 := by
  simp [Finset.bipartiteAbove]
  simp [← card_neighborFinset_eq_degree ]
  rw [← Sym2.card_image_offDiag]
  congr
  ext x
  simp [DoubleCountingRel]
  induction' x using Sym2.inductionOn with A B
  constructor
  · intro one
    use A
    use B
    constructor
    constructor
    apply one.2 A _
    simp
    constructor
    apply one.2 B _
    simp
    intro con
    apply one.1
    simpa
    rfl
  · intro two
    --rcases two with ⟨a, ⟨b ,⟨ua ,⟨ub, anb⟩ ⟩, ⟨eq⟩ ⟩⟩,
    cases' two with a h
    cases' h with b h
    cases' h with h eq
    constructor
    intro con
    apply h.2.2
    rw [← eq] at con
    simpa using con
    intro y ydef
    rw [← eq] at ydef
    rw [Sym2.mem_iff] at ydef
    obtain ydef | ydef := ydef
    rw [ydef]
    exact h.1
    rw [ydef]
    exact h.2.1

/-- We show that for distinct vertices `v` and `w`,
the number of vertices in relation with
the pair they make up, is at most 1.
-/
theorem double_count_below (G : SimpleGraph V) (hG : C4Free G) (v w : V) (vnw : v ≠ w) :
    ((Finset.bipartiteBelow (DoubleCountingRel G) univ) s(v, w)).card ≤ 1 := by
  have := c4Free_common_neighbours G hG v w vnw
  simp [Finset.bipartiteBelow, DoubleCountingRel]
  dsimp [commonNeighbors, neighborSet] at this
  simp at this
  rw [← filter_and] at this
  convert this using 4
  rw [adj_comm]
  nth_rw 2 [adj_comm]

open scoped BigOperators

/-- The sum of the number of vertices in relation with a given pair,
taken over all pairs of distinct vertices, is less then
"|V| choose 2"
-/
theorem double_count_below_bound (G : SimpleGraph V) (hG : C4Free G) :
    ∑ e in {e : Sym2 V | ¬e.IsDiag}.toFinset,
        ((Finset.bipartiteBelow (DoubleCountingRel G) univ) e).card ≤
      (Fintype.card V).choose 2 := by
  rw [← Sym2.card_subtype_not_diag]
  rw [← Finset.card_univ]
  rw [card_eq_sum_ones]
  rw [← @sum_subtype _ _ (fun e : Sym2 V => ¬e.IsDiag) _ {e : Sym2 V | ¬e.IsDiag}.toFinset _
      fun e : Sym2 V => 1]
  swap
  · intro e
    simp
  apply sum_le_sum
  intro e
  apply Sym2.inductionOn e
  intro x y xydef
  dsimp
  apply double_count_below G hG
  simp at xydef
  apply xydef

/-- We make use of double counting and the previous bounds
to get a relation linking degrees and the graph's order
-/
theorem first_ineq (G : SimpleGraph V) (hG : C4Free G) :
    ∑ u in (univ : Finset V), (G.degree u).choose 2 ≤ (Fintype.card V).choose 2 := by
  simp_rw [← double_count_above']
  rw [@sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _ _ (DoubleCountingRel G)
      (univ : Finset V) {e : Sym2 V | ¬e.IsDiag}.toFinset _]
  apply double_count_below_bound G hG

/-- A technical rewrite we separated from `first_ineq_rw` -/
theorem tec_stuff (n : ℕ) : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
  nth_rw 2 [← Nat.mod_add_div (n * (n - 1)) 2]
  rw [self_eq_add_left]
  rw [Nat.mul_mod]
  have : n % 2 * ((n - 1) % 2) = 0 := by
    rw [mul_eq_zero]
    induction' n with n ih
    left
    decide
    obtain ih | ih := ih
    right
    rw [Nat.add_one_sub_one]
    exact ih
    by_cases q : n = 0
    rw [q]
    decide
    rw [← Ne] at q
    rw [← Nat.one_le_iff_ne_zero] at q
    left
    have id : n + 1 = n - 1 + 2 := by omega
    rw [id]
    rw [Nat.add_mod]
    rw [ih]
    decide
  rw [this]
  decide

--#find _ → (_ - _ ≤ _ ↔ _ ≤ _ + _) -- timeout
/-- We rewrite the first inequality with
some algebraic manipulations and previous
equalities.
-/
theorem first_ineq_rw (G : SimpleGraph V) (hG : C4Free G) :
    ∑ u in (univ : Finset V), G.degree u ^ 2 ≤
      Fintype.card V * (Fintype.card V - 1) + ∑ u in (univ : Finset V), G.degree u := by
  have := first_ineq G hG
  rw [Nat.choose_two_right] at this
  simp_rw [Nat.choose_two_right] at this
  have that : Monotone fun x => 2 * x := by simp [Monotone]
  apply_fun fun x => 2 * x at this  using that
  rw [mul_sum] at this
  rw [tec_stuff (Fintype.card V)] at this
  simp_rw [tec_stuff] at this
  rw [Nat.mul_sub_left_distrib] at this
  simp_rw [Nat.mul_sub_left_distrib] at this
  simp_rw [← pow_two, mul_one] at this
  have tec : ∀ i : V, G.degree i ≤ G.degree i ^ 2 := by
    intro i
    by_cases q : G.degree i = 0
    rw [q]
    decide
    nth_rw 1 [← mul_one (G.degree i)]
    rw [pow_two]
    rw [mul_le_mul_left]
    rw [Nat.one_le_iff_ne_zero]
    apply q
    rw [Nat.lt_iff_add_one_le]
    rw [zero_add]
    rw [Nat.one_le_iff_ne_zero]
    apply q
  rw [Finset.sum_tsub_distrib] at this
  swap
  exact tec
  rw [sub_le_iff_le_add] at this
  rw [Nat.mul_sub_left_distrib]
  rw [← pow_two, mul_one]
  exact this
  apply sum_le_sum
  intro i idef
  exact tec i

/-- We use a technique consisting in applying Cauchy-Schwartz
with the all 1 vector to get a fruther inequality in our context.
-/
theorem Cauchy_Schwartz_in_action (G : SimpleGraph V) :
    ((∑ u in (univ : Finset V), G.degree u) ^ 2 : ℤ) ≤
      Fintype.card V * ∑ u in (univ : Finset V), G.degree u ^ 2 := by
  have := sum_mul_sq_le_sq_mul_sq (univ : Finset V) (fun u => (G.degree u : ℤ)) (fun u => (1 : ℤ))
  simp_rw [one_pow, mul_one] at this
  rw [← Finset.card_univ]
  simp_rw [card_eq_sum_ones (univ : Finset V)]
  rw [mul_comm]
  --exact this, --coersion
  push_cast
  simpa

theorem second_ineq (G : SimpleGraph V) (hG : C4Free G) :
    ((∑ u in (univ : Finset V), G.degree u) ^ 2 : ℤ) ≤
      Fintype.card V ^ 2 * (Fintype.card V - 1) +
        Fintype.card V * ∑ u in (univ : Finset V), G.degree u := by
  apply le_trans (Cauchy_Schwartz_in_action G)
  rw [pow_two]
  rw [mul_assoc]
  rw [← mul_add]
  by_cases q : 0 < Fintype.card V
  rw [mul_le_mul_left]
  swap
  rw [Nat.cast_pos]
  exact q
  have := first_ineq_rw G hG
  rw [← @Nat.cast_le ℤ _ _ _ _] at this
  push_cast at this
  exact this
  have : Fintype.card V = 0 := by linarith
  rw [this]
  simp

theorem third_ineq (G : SimpleGraph V) (hG : C4Free G) :
    (4 * G.edgeFinset.card ^ 2 : ℝ) ≤
      Fintype.card V ^ 2 * (Fintype.card V - 1) + Fintype.card V * 2 * G.edgeFinset.card := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num1]
  rw [← mul_pow]
  rw [mul_assoc]
  have := sum_degrees_eq_twice_card_edges G
  -- here is where "2|E| = ∑ deg" comes into play
  apply_fun fun x => (x : ℝ) at this
  push_cast at this
  rw [← show (2 : ℝ) = 0 + 1 + 1 by norm_num] at this
  rw [← this]
  clear this
  have := second_ineq G hG
  have that : Monotone fun x : ℤ => (x : ℝ) := by simp [Monotone]
  apply_fun fun x => (x : ℝ) at this  using that
  simp at this
  exact this

/-- We isloate the algebraic manipulations needed to get
`max_edges_of_c4_free_Istvan_Reiman` from our previous
inequality, to ease noatation.
-/
theorem max_edges_of_c4_free_Istvan_Reiman_pre (a b : ℕ)
    (ineq : (4 * a ^ 2 : ℝ) ≤ b ^ 2 * (b - 1) + b * 2 * a) :
    (a : ℤ) ≤ ⌊(b / 4 : ℝ) * (1 + Real.sqrt (4 * b - 3))⌋ := by
  rw [Int.le_floor]
  simp only [Int.cast_ofNat]
  rw [mul_add]
  rw [mul_one]
  apply le_add_of_sub_left_le
  -- We make use of the canoncic/normal form of 2nd degree equations
  have canonic : (4 : ℝ) * (a - b / 4) ^ 2 ≤ b ^ 2 / 4 * (1 + (4 * b - 4)) := by
    rw [pow_two, sub_mul, mul_sub, mul_sub, ← pow_two]
    cancel_denoms
    simp_rw [mul_assoc]
    rw [← mul_add]
    rw [mul_le_mul_left (show 0 < (4 : ℝ) by norm_num)]
    cancel_denoms
    ring_nf
    rw [show (4 * ↑b - 4 : ℝ) = 4 * (↑b - 1) by rw [mul_sub]; rw [mul_one]]
    rw [add_mul]
    rw [show (16 : ℝ) = 4 * 4 by norm_num]
    rw [show (8 : ℝ) = 4 * 2 by norm_num]
    simp_rw [mul_assoc]
    rw [← mul_add]
    rw [mul_le_mul_left (show 0 < (4 : ℝ) by norm_num)]
    rw [← pow_two]
    rw [← mul_assoc]
    nth_rw 2 [mul_comm]
    nth_rw 3 [mul_comm]
    rw [← mul_assoc]
    exact ineq
  rw [← mul_le_mul_left (show 0 < (2 : ℝ) by norm_num)]
  nth_rw 1 [show (4 : ℝ) = 2 ^ 2 by norm_num] at canonic
  rw [← mul_pow] at canonic
  replace canonic := Real.le_sqrt_of_sq_le canonic
  rw [Real.sqrt_mul] at canonic
  rw [← mul_assoc]
  have one : 2 * (↑b / 4) = Real.sqrt (↑b ^ 2 / 4) := by
    rw [Real.sqrt_div]
    rw [Real.sqrt_sq _]
    rw [mul_div_left_comm]
    rw [show (2 / 4 : ℝ) = 1 / 2 by norm_num]
    rw [show (4 : ℝ) = 2 * 2 by norm_num]
    rw [Real.sqrt_mul_self (show (0 : ℝ) ≤ 2 by norm_num)]
    ring
    apply Nat.cast_nonneg
    apply sq_nonneg
  rw [one]
  have two : (1 : ℝ) + (4 * ↑b - 4) = 4 * ↑b - 3 := by linarith
  simp_rw [← two]
  exact canonic
  apply div_nonneg
  apply sq_nonneg
  norm_num

-- Deriving the canonic form with `ring`
example (a b : ℕ) :
    (4 * a ^ 2 : ℝ) - b ^ 2 * (b - 1) - b * 2 * a =
      (4 : ℝ) * (a - b / 4) ^ 2 - b ^ 2 / 4 * (1 + (4 * b - 4)) := by ring

/-- If a 4-cycle-free graph, the number of edges is upper-bounded by the following expression in the number of vertices |V|:
⌊(|V|/ 4)(1 + real.sqrt (4*|V| - 3))⌋
-/
theorem max_edges_of_c4Free_Istvan_Reiman (G : SimpleGraph V) (hG : C4Free G) :
    (G.edgeFinset.card : ℤ) ≤
      ⌊(Fintype.card V / 4 : ℝ) * (1 + Real.sqrt (4 * Fintype.card V - 3))⌋ := by
  apply max_edges_of_c4_free_Istvan_Reiman_pre G.edgeFinset.card (Fintype.card V)
  exact third_ineq G hG

/-- The converse to `c4_free_common_neightbours`.
If any two vertices have at most one common neighbour,
then the graph is 4-cycle-free.
-/
theorem commonNeighbors_c4Free (G : SimpleGraph V)
    (h : ∀ v w, v ≠ w → (commonNeighbors G v w).toFinset.card ≤ 1) : C4Free G := by
  revert h
  rw [C4Free]
  contrapose!
  -- we show this by contraposition
  intro C
  rcases C with ⟨v, ⟨cyc, ⟨cyc_cycle, cyc_len⟩⟩⟩
  -- We unfold the cycle
  cases' cyc with _ _ a _ av cyc
  exfalso; exact cyc_cycle.not_of_nil
  cases' cyc with _ _ b _ ba cyc
  · simp [SimpleGraph.Walk.length_nil, zero_add, SimpleGraph.Walk.length_cons] at cyc_len
  cases' cyc with _ _ c _ bc cyc
  exfalso;
  simp only [SimpleGraph.Walk.length_nil, zero_add, SimpleGraph.Walk.length_cons] at cyc_len ;
  norm_num at cyc_len
  cases' cyc with _ _ d _ dc cyc
  exfalso;
  simp only [SimpleGraph.Walk.length_nil, zero_add, SimpleGraph.Walk.length_cons] at cyc_len ;
  norm_num at cyc_len
  simp at cyc_len
  --norm_num at cyc_len, --fails, hence:
  have : cyc.length = 0 := by linarith
  replace this := Walk.eq_of_length_eq_zero this
  -- We will show that two vertices on oppsite sides of
  -- the cycles have at least two neighbours in common
  use v;
  use b
  simp [Walk.isCycle_def] at cyc_cycle
  push_neg at cyc_cycle
  constructor
  exact cyc_cycle.1.2.1.2
  have that : {a, c} ⊆ (G.commonNeighbors v b).toFinset := by
    intro x xdef
    rw [mem_insert] at xdef
    rw [mem_singleton] at xdef
    obtain rfl | rfl := xdef
    simp [commonNeighbors]
    exact ⟨av, G.adj_symm ba⟩
    simp [commonNeighbors]
    rw [this] at dc
    exact ⟨G.adj_symm dc, bc⟩
  --apply_fun finset.card at that using finset.card_mono, --fails
  have thot : ({a, c} : Finset V).card = 2 := by
    rw [card_insert_of_not_mem]
    rw [card_singleton]
    intro con
    rw [mem_singleton] at con
    exact cyc_cycle.1.1.2.1.2 con
  apply lt_of_lt_of_le (show 1 < 2 by norm_num)
  rw [← thot]
  apply card_le_card that

variable (p : ℕ) [Fact p.Prime]

/-
Note : instance [nat.prime p] is a thing, but raises error
because `zmod p` isn't recognized as a field
-/
/-- Two vertices (points of the pejective space), are connected by an edge iff they're orthogonal to one another.
-/
def EdgeRelation (v w : Projectivization (ZMod p) (Fin 3 → ZMod p)) :=
  v ≠ w ∧ Matrix.dotProduct v.rep w.rep = 0

/-- The extremal graph that will be used to show that the bound
from `max_edges_of_c4_free_Istvan_Reiman` is tight.
-/
def extremalGraph : SimpleGraph (Projectivization (ZMod p) (Fin 3 → ZMod p))
    where
  Adj := EdgeRelation p
  symm := by
    rw [Symmetric]
    intro v w rel
    dsimp only [EdgeRelation] at *
    constructor
    exact Ne.symm rel.1
    rw [Matrix.dotProduct_comm]
    exact rel.2
  loopless := by
    rw [Irreflexive]
    intro v
    dsimp [EdgeRelation]
    push_neg
    intro con
    exfalso
    exact con (Eq.refl v)

/-- A rewrite lemma characterizing neighbours in terms of orthogonality
-/
theorem neighbor_extremalGraph (v w : Projectivization (ZMod p) (Fin 3 → ZMod p)) :
    v ∈ (extremalGraph p).neighborSet w ↔ v ≠ w ∧ Matrix.dotProduct v.rep w.rep = 0 := by
  rw [mem_neighborSet]
  dsimp only [extremalGraph, EdgeRelation]
  rw [Matrix.dotProduct_comm, ne_comm]

instance reminder : Fintype (ZMod p) :=
  inferInstance

-- turns out only this instance is needed for .to_finset not to fail in Zp3_fin
noncomputable instance zp3Fin : Fintype (Projectivization (ZMod p) (Fin 3 → ZMod p)) := by--infer_instance --fails
  apply
    @Quotient.fintype { v : Fin 3 → ZMod p // v ≠ 0 }
      (by
        apply Fintype.subtype {v : Fin 3 → ZMod p | v ≠ 0}.toFinset
        intro x
        simp only [true_and, Finset.mem_univ, Set.toFinset_congr, iff_self,
          Set.toFinset_setOf, Ne, Finset.mem_filter])
      (projectivizationSetoid (ZMod p) (Fin 3 → ZMod p)) _

/-- To make use of orthogonality related theorems,
we need to remind ourselves that the dot-product
is a bilinear form.
-/
def dotp : LinearMap.BilinForm (ZMod p) (Fin 3 → ZMod p)
    where
  bilin x y := Matrix.dotProduct x y
  bilin_add_left := by apply Matrix.add_dotProduct
  bilin_add_right := by apply Matrix.dotProduct_add
  bilin_smul_left := by apply Matrix.smul_dotProduct
  bilin_smul_right := by apply Matrix.dotProduct_smul

/-- For two linearly independent vectors `v` and `w`, the property that
`u` is orthogonal to their span is equivalent to `u` being
orthogonal to `v` and `w`.
-/
theorem ortho_span_pair_iff (v w u : Fin 3 → ZMod p) (h : LinearIndependent (ZMod p) ![v, w]) :
    u ∈ BilinForm.orthogonal (dotp p) (Submodule.span (ZMod p) {v, w}) ↔
      (dotp p).bilin v u = 0 ∧ (dotp p).bilin w u = 0 := by
  constructor
  · intro susp
    rw [BilinForm.mem_orthogonal_iff] at susp
    simp_rw [BilinForm.isOrtho_def] at susp
    constructor
    · apply susp v
      rw [Submodule.mem_span_insert]
      use(1 : ZMod p)
      use(0 : Fin 3 → ZMod p)
      constructor
      apply Submodule.zero_mem _
      simp only [add_zero, eq_self_iff_true, one_smul]
    · apply susp w
      rw [Set.pair_comm v w]
      rw [Submodule.mem_span_insert]
      use(1 : ZMod p); use(0 : Fin 3 → ZMod p)
      constructor
      apply Submodule.zero_mem _
      simp only [add_zero, eq_self_iff_true, one_smul]
  · rintro ⟨ov, ow⟩
    rw [BilinForm.mem_orthogonal_iff]
    simp only [BilinForm.isOrtho_def]
    intro x xdef
    apply Submodule.span_induction xdef
    -- generating vectors
    · intro y ydef
      rw [Set.mem_insert_iff] at ydef
      cases ydef
      rw [ydef]
      apply ov
      rw [Set.mem_singleton_iff] at ydef
      rw [ydef]
      apply ow
    -- zero
    · apply BilinForm.zero_left
    -- add
    · intro y z yprop zprop
      rw [BilinForm.add_left]
      rw [yprop, zprop]
      norm_num
    -- smul
    · intro a y yprop
      simp only [BilinForm.smul_left, mul_eq_zero]
      right; exact yprop

/-- The dot product is reflexive (crtl-click to see what it means)--/
theorem dotp_isRefl : (dotp p).IsRefl := by
  apply BilinForm.IsSymm.isRefl
  intro x y
  dsimp [dotp]
  apply Matrix.dotProduct_comm

/-- The dot product is nondegenerate
(there is no vector orthogonal to all vectors)
-/
theorem dotp_nondegenerate : (dotp p).orthogonal ⊤ = ⊥ := by
  ext x
  simp only [BilinForm.mem_orthogonal_iff, Submodule.mem_bot]
  dsimp [BilinForm.isOrtho_def]
  dsimp [dotp]
  constructor
  · intro forth
    ext i
    dsimp
    specialize forth (Pi.single i 1) Submodule.mem_top
    rw [Matrix.dotProduct_comm] at forth
    rw [Matrix.dotProduct_single] at forth
    rw [mul_one] at forth
    exact forth
  · intro back
    intro y useless
    rw [back]
    apply Matrix.dotProduct_zero

/-- In (ℤ_p)^3, the dimension of the orthogonal complement
to the span of 2 linearly independent vectors is 1.
-/
theorem dim_of_ortho (v w : Fin 3 → ZMod p) (h : LinearIndependent (ZMod p) ![v, w]) :
    FiniteDimensional.finrank (ZMod p)
        ↥(BilinForm.orthogonal (dotp p) (Submodule.span (ZMod p) {v, w})) =
      1 := by
  have main_id :=
    @BilinForm.finrank_add_finrank_orthogonal _ _ _ _ _ _ _ (Submodule.span (ZMod p) {v, w})
      (dotp_isRefl p)
  rw [FiniteDimensional.finrank_fin_fun] at main_id
  have tec : {v, w} = Set.range ![v, w] := by
    simp only [eq_self_iff_true, Matrix.range_cons_cons_empty]
  rw [tec] at main_id
  rw [finrank_span_eq_card h] at main_id
  rw [← tec] at main_id
  clear tec
  rw [show Fintype.card (Fin (Nat.succ 1)) = 2 by decide] at main_id
  rw [dotp_nondegenerate] at main_id
  rw [inf_bot_eq] at main_id
  simp only [add_zero, finrank_bot] at main_id
  linarith

/-- A rewrite lemma charcterising equality in the projective space
via linear independence of representatives.
-/
theorem rw_tec (v w : ℙ (ZMod p) (Fin 3 → ZMod p)) :
    v ≠ w ↔ LinearIndependent (ZMod p) ![v.rep, w.rep] := by
  have : Projectivization.rep ∘ ![v, w] = ![v.rep, w.rep] := by
    ext i y
    fin_cases i
    dsimp; rfl
    dsimp; rfl
  rw [← Projectivization.independent_pair_iff_neq]
  rw [Projectivization.independent_iff]
  rw [this]

/-- The extremal graph we built is 4-cycle-free !
-/
theorem extremalGraph_c4Free : C4Free (extremalGraph p) := by
  -- We use the charcterization in terms of common neighbours
  apply commonNeighbors_c4Free (extremalGraph p)
  intro v w vnw
  -- We then proceed by contradiction, so as to get
  -- common neighbours `a` and `b`
  by_contra! con
  rw [Nat.lt_iff_add_one_le] at con
  norm_num at con
  obtain ⟨a, ⟨b, ⟨meh, ⟨meeh, absub⟩⟩⟩⟩ := pair_of_two_le_card con
  have adef := a.prop
  have bdef := b.prop
  simp_rw [commonNeighbors_eq] at adef bdef
  rw [Set.mem_inter_iff] at adef bdef
  -- We translate between neighbours and orthogonals
  simp_rw [neighbor_extremalGraph] at adef bdef
  have bo :
    (b : ℙ (ZMod p) (Fin 3 → ZMod p)).rep ∈
      BilinForm.orthogonal (dotp p) (Submodule.span (ZMod p) {v.rep, w.rep}) := by
    rw [ortho_span_pair_iff]
    dsimp [dotp]
    nth_rw 1 [Matrix.dotProduct_comm]
    nth_rw 2 [Matrix.dotProduct_comm]
    exact ⟨bdef.1.2, bdef.2.2⟩
    exact (rw_tec p v w).mp vnw
  have ao :
    (a : ℙ (ZMod p) (Fin 3 → ZMod p)).rep ∈
      BilinForm.orthogonal (dotp p) (Submodule.span (ZMod p) {v.rep, w.rep}) := by
    rw [ortho_span_pair_iff]
    dsimp [dotp]
    nth_rw 1 [Matrix.dotProduct_comm]
    nth_rw 2 [Matrix.dotProduct_comm]
    exact ⟨adef.1.2, adef.2.2⟩
    exact (rw_tec p v w).mp vnw
  -- We recall the dimension of the orthogonal
  have dim_o := dim_of_ortho p v.rep w.rep ((rw_tec p v w).mp vnw)
  -- We recall the charcterization of 1-dimensional spaces
  have dim_o_char :=
    @finrank_eq_one_iff_of_nonzero' (ZMod p)
      (↥((dotp p).orthogonal (Submodule.span (ZMod p) {v.rep, w.rep}))) _ _ _
  -- We derive from it that `a` and `b` are dependent
  specialize
    dim_o_char ⟨b.val.rep, bo⟩
      (by
        intro con'
        rw [Subtype.ext_iff_val] at con'
        dsimp at con'
        exact (Projectivization.rep_nonzero b.val) con')
  rw [dim_o_char] at dim_o
  obtain ⟨sc, eq⟩ := dim_o ⟨a.val.rep, ao⟩
  simp only [SetLike.mk_smul_mk, Subtype.mk_eq_mk] at eq
  -- Yet, we recall that `a ≠ b` meant that they were independent
  rw [Ne, not_iff_not.mpr Subtype.ext_iff_val, ← Ne] at absub
  rw [rw_tec p a.val b.val] at absub
  rw [linearIndependent_fin2] at absub
  simp only [Matrix.head_cons, Ne, Matrix.cons_val_one] at absub
  apply absub.2 sc
  simp only [Matrix.cons_val_zero]
  exact Eq

-- To be continiued
