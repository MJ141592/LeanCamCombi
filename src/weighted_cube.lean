/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import probability.ident_distrib
import mathlib.measure
import probability.probability_mass_function.constructions

/-
We want to formlate a sequence of iid Bernoulli random variables
-/

open measure_theory probability_theory
open_locale measure_theory probability_theory ennreal nnreal

variables {ι Ω : Type*} [measure_space Ω]

/-- A sequence iid. real valued Bernoulli random variables with parameter `p ≤ 1`. -/
def bernoulli_seq (X : Ω → ι → bool) (p : ℝ≥0) : Prop :=
Indep_fun (λ _, infer_instance) (λ i ω, X ω i) ℙ ∧
∀ i, measure.map (λ ω, X ω i) ℙ = (pmf.bernoulli (min p 1) $ min_le_right _ _).to_measure

variables {X : Ω → ι → bool} {p : ℝ≥0}

namespace bernoulli_seq

def bool.measurable_space : measurable_space bool := ⊤

local attribute [instance] bool.measurable_space

@[protected]
lemma Indep_fun (h : bernoulli_seq X p) :
  Indep_fun (λ _, infer_instance) (λ i ω, X ω i) ℙ :=
h.1

@[protected]
lemma map (h : bernoulli_seq X p) (i : ι) : measure.map (λ ω, X ω i) ℙ =
  (pmf.bernoulli (min p 1) $ min_le_right _ _).to_measure := h.2 i

@[protected]
lemma ae_measurable [ne_zero (ℙ : measure Ω)] (h : bernoulli_seq X p) (i : ι) :
  ae_measurable (λ ω, X ω i) :=
begin
  classical,
  suffices : (pmf.bernoulli (min p 1) $ min_le_right _ _).to_measure ≠ 0,
  { rw [← h.map i, measure.map] at this,
    refine (ne.dite_ne_right_iff $ λ hX hzero, _).1 this,
    rw measure.mapₗ_eq_zero_iff hX.measurable_mk at hzero,
    exact ne_zero.ne _ hzero },
  exact ne_zero.ne _
end

@[protected]
lemma ident_distrib [ne_zero (ℙ : measure Ω)] (h : bernoulli_seq X p) (i j : ι) :
  ident_distrib (λ ω, X ω i) (λ ω, X ω j) :=
{ ae_measurable_fst := h.ae_measurable i,
  ae_measurable_snd := h.ae_measurable j,
  map_eq := (h.map i).trans (h.map j).symm }

end bernoulli_seq
