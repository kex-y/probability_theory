import measure_theory.decomposition.radon_nikodym
import measure_theory.integral.set_integral
import 

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α β : Type*} {m : measurable_space α}

lemma ennreal.of_real_le_norm (r : ℝ) : ennreal.of_real r ≤ ∥r∥₊ :=
begin
  by_cases hr : r ≤ 0,
  { rw [ennreal.of_real_eq_zero.2 hr],
    simp only [zero_le', ennreal.coe_nonneg] },
  { rw [real.nnnorm_of_nonneg (le_of_not_le hr), ennreal.of_real, ennreal.coe_le_coe, 
        ← nnreal.coe_le_coe, real.coe_to_nnreal r (le_of_not_le hr), subtype.coe_mk] }
end

namespace measure_theory

include m

lemma integrable.sum_integrable {f : α → ℝ} {μ : ℕ → measure α} 
  (hμ : integrable f (measure.sum μ)) (n : ℕ) : integrable f (μ n) := 
begin
  sorry
end

namespace measure

open topological_space

section with_density'

/- Show s ↦ ∫ x in s, f x ∂μ form a signed measure. -/

variables {E : Type*} [normed_group E] [measurable_space E] [second_countable_topology E]
  [normed_space ℝ E] [complete_space E] [borel_space E]

variables {μ ν : measure α}

-- lemma lintegral_nonneg (f : α → ℝ≥0∞) : 0 ≤ ∫⁻ x, f x ∂μ :=
-- begin
--   rw [← @lintegral_zero _ _ μ],
--   exact lintegral_mono (λ x, zero_le _),
-- end

lemma tsum_lintegral_of_real_lt_top {f : α → ℝ} {μ : ℕ → measure α} 
  (hμ : integrable f (sum μ)) : ∑' n, ∫⁻ x, ennreal.of_real (f x) ∂ (μ n) < ⊤ :=
begin
  obtain ⟨-, hlt⟩ := hμ,
  rw [has_finite_integral, lintegral_sum_measure] at hlt,
  refine lt_of_le_of_lt (tsum_le_tsum _ ennreal.summable ennreal.summable) hlt,
  exact λ n, lintegral_mono (λ x, ennreal.of_real_le_norm (f x)),
end

lemma integral_sum_measure
  {f : α → ℝ} (μ : ℕ → measure α) (hμ : integrable f (sum μ)) :
  ∫ x, f x ∂(sum μ) = ∑' n, ∫ x, f x ∂(μ n) :=
begin
  have h₁ := ennreal.summable_to_real (tsum_lintegral_of_real_lt_top hμ).ne,
  have h₂ := ennreal.summable_to_real 
    (tsum_lintegral_of_real_lt_top (integrable_neg_iff.2 hμ)).ne,
  rw integral_eq_lintegral_pos_part_sub_lintegral_neg_part hμ,
  rw [lintegral_sum_measure, lintegral_sum_measure],
  erw [ennreal.tsum_to_real_eq, ennreal.tsum_to_real_eq, ← tsum_sub h₁ h₂], 
  { refine tsum_congr (λ n, _),
    erw [← integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hμ.sum_integrable n)] };
  sorry
end

lemma integral_Union {f : α → ℝ} {s : ℕ → set α}
  (hs₁ : ∀ n, measurable_set (s n))
  (hs₂ : pairwise (disjoint on s))
  (hs₃ : integrable f (sum (λ n, μ.restrict (s n)))) :
  ∫ x in ⋃ n, s n, f x ∂μ = ∑' n, ∫ x in s n, f x ∂μ :=
begin
  rw [restrict_Union hs₂ hs₁, integral_sum_measure],
  exact hs₃,
end

def with_density_vector_measure {m : measurable_space α} (μ : measure α) (f : α → ℝ) :
  vector_measure α ℝ :=
if hf : integrable f μ then
{ measure_of' := λ s, if measurable_set s then ∫ x in s, f x ∂μ else 0,
  empty' := by simp,
  not_measurable' := λ s hs, if_neg hs,
  m_Union' := λ s hs₁ hs₂,
  begin
    rw integral_Union hs₁ hs₂,
    conv { congr, funext, rw if_pos (hs₁ _), skip, rw if_pos (measurable_set.Union hs₁) };
    sorry, sorry
  end }
else 0

/-
Alternative definition of `with_density_vector_measure`: Given `f : α → ℝ`, define
`μ.with_density_vector_measure f = μ.with_density f⁺ - μ.with_density f⁻`
-/

end with_density'

end measure

end measure_theory
