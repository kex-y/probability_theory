import singular
import sigma_finite

/- 
This file contains the definition of the countable sum of measures and 
extends the Lebesgue decomposition and Radon-Nikodym theorem to σ-finite 
measures.
-/

noncomputable theory
open_locale classical big_operators nnreal ennreal

variables {α β : Type*} [measurable_space α]

open measure_theory

lemma tsum_measure_empty {μ : ℕ → measure α} : ∑' n, μ n ∅ = 0 :=
begin
  convert tsum_zero,
  { exact funext (λ n, measure_empty) },
  { apply_instance },
end

lemma tsum_measure_m_Union {μ : ℕ → measure α} ⦃f : ℕ → set α⦄
  (hf₁ : ∀ (i : ℕ), measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  ∑' (n : ℕ), (μ n) (⋃ (i : ℕ), f i) = ∑' (i n : ℕ), (μ n) (f i) :=
begin
  rw tsum_comm',
  { exact tsum_congr (λ n, measure_Union hf₂ hf₁) },
  exacts [ennreal.summable, λ _, ennreal.summable, λ _, ennreal.summable]
end

def tsum_measure (μ : ℕ → measure α) : measure α := 
measure.of_measurable (λ s hs, ∑' n, μ n s) tsum_measure_empty tsum_measure_m_Union

lemma tsum_measure_apply {μ : ℕ → measure α} (i : set α) (hi : measurable_set i) : 
  tsum_measure μ i = ∑' n, μ n i := 
measure.of_measurable_apply i hi

lemma tsum_measure_zero : tsum_measure (0 : ℕ → measure α) = 0 :=
begin
  refine measure_theory.measure.ext (λ i hi, _),
  rw [tsum_measure_apply i hi],
  exact tsum_zero
end

lemma tsum_measure_add {μ ν : ℕ → measure α} : 
  tsum_measure μ + tsum_measure ν = tsum_measure (μ + ν) := 
begin
  refine measure_theory.measure.ext (λ i hi, _),
  rw [measure.coe_add, pi.add_apply, tsum_measure_apply i hi, 
      tsum_measure_apply i hi, tsum_measure_apply i hi],
  exact (tsum_add (ennreal.summable) (ennreal.summable)).symm,
end

namespace signed_measure

local infix ` . `:max := measure.with_density

/-- The Lebesgue decomposition theorem extended to σ-finite measures. -/
theorem exists_singular_with_density' 
  (μ ν : measure α) [sigma_finite μ] [sigma_finite ν] :
  ∃ (ν₁ ν₂ : measure α) (hν : ν = ν₁ + ν₂), ν₁ ⊥ μ ∧ 
  ∃ (f : α → ℝ≥0∞) (hf : measurable f), ν₂ = μ . f := 
begin

  obtain ⟨S, hS⟩ := exists_disjoint_finite_spanning_sets_in μ,
  obtain ⟨T, hT⟩ := exists_disjoint_finite_spanning_sets_in ν,

  have : ∀ n : ℕ, ∃ (ν₁ ν₂ : measure α) (hν : ν.restrict (T.set n) = ν₁ + ν₂), 
    ν₁ ⊥ μ.restrict (S.set n) ∧ ∃ (f : α → ℝ≥0∞) (hf : measurable f), 
    ν₂ = μ.restrict (S.set n) . f, 
  { intro n,
    haveI : finite_measure (μ.restrict (S.set n)) := 
      @restrict.finite_measure _ _ _ μ (fact_iff.2 (S.finite n)),
    haveI : finite_measure (ν.restrict (T.set n)) := 
      @restrict.finite_measure _ _ _ ν (fact_iff.2 (T.finite n)),
    exact exists_singular_with_density _ _ },
  
  choose ν₁ ν₂ hνa hνb f hνc hνd using this,

  refine ⟨tsum_measure ν₁, tsum_measure ν₂, _, _, _⟩,
  { rw tsum_measure_add,
    refine measure_theory.measure.ext (λ i hi, _),
    rw [tsum_measure_apply i hi],
    simp only [measure.coe_add, pi.add_apply],
    rw [show ∑' n, (ν₁ n i + ν₂ n i) = ∑' n, (ν.restrict (T.set n)) i, 
        by exact tsum_congr (λ n, (hνa n).symm ▸ rfl), 
        ← measure.restrict_Union_apply hT T.set_mem hi, T.spanning, 
        measure.restrict_univ] },
  { choose i hi₁ hi₂ hi₃ using hνb,
    refine ⟨⋂ n, i n, measurable_set.Inter hi₁, _, _⟩,
    { rw tsum_measure_apply _ (measurable_set.Inter hi₁), 
      convert tsum_zero,
      exact funext (λ n, nonpos_iff_eq_zero.1 
        (hi₂ n ▸ (measure_mono (set.Inter_subset i n)))),
      apply_instance },
    { --rw [← @measure.restrict_univ _ _ μ, ← S.spanning, measure.restrict_apply, 
      rw [set.compl_Inter],
      sorry
    }
   },
  { sorry }
end

end signed_measure