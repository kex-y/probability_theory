import signed_radon_nikodym
import measure_theory.measure.lebesgue

noncomputable theory
open_locale classical measure_theory nnreal ennreal

section

open measure_theory measure_theory.measure

variables {α β : Type*} [measurable_space α] [measurable_space β] 

lemma measure_theory.measure.is_finite_measure.map (μ : measure α) [is_finite_measure μ] 
  {f : α → β} (hf : measurable f) : is_finite_measure (map f μ) :=
⟨by { rw [map_apply hf measurable_set.univ, set.preimage_univ], exact measure_lt_top μ _ }⟩

end

namespace measure_theory

open topological_space measure

variables {α : Type*} [measurable_space α]
variables {E : Type*} [normed_group E] [measurable_space E] [second_countable_topology E]
  [normed_space ℝ E] [complete_space E] [borel_space E] 

class has_pdf (X : α → E) (ℙ : measure α . volume_tac) (μ : measure E . volume_tac) : Prop := 
(pdf : ∃ f : E → ℝ≥0∞, map X ℙ = μ.with_density f)

def pdf (X : α → E) (ℙ : measure α) (μ : measure E) [hX : has_pdf X ℙ μ] : E → ℝ≥0∞ := 
classical.some hX.pdf

lemma pdf_spec {X : α → E} (ℙ : measure α) (μ : measure E) [hX : has_pdf X ℙ μ] :
  measure.map X ℙ = μ.with_density (pdf X ℙ μ) :=
classical.some_spec hX.pdf

lemma pdf_spec' {X : α → E} (ℙ : measure α) (μ : measure E) 
  [hX : has_pdf X ℙ μ] {s : set E} (hs : measurable_set s) :
  measure.map X ℙ s = ∫⁻ x in s, pdf X ℙ μ x ∂μ := 
by rw [← with_density_apply _ hs, pdf_spec ℙ μ]

namespace pdf

variables {ℙ : measure α} {μ : measure E}

section is_probability_measure

variables [is_probability_measure ℙ] {X : α → E} [has_pdf X ℙ μ] (hX : measurable X)

include hX

lemma integral_eq_one : ∫⁻ x, pdf X ℙ μ x ∂μ = 1 :=
begin
  rw [← set_lintegral_univ, ← pdf_spec' ℙ μ measurable_set.univ, 
      measure.map_apply hX measurable_set.univ, set.preimage_univ, measure_univ],
end

end is_probability_measure

section real

variables [is_finite_measure ℙ] {X : α → ℝ} (hX : measurable X)

include hX

lemma has_pdf_iff : has_pdf X ℙ ↔ measure.map X ℙ ≪ (volume : measure ℝ) := 
begin
  split,
  { introI hX,
    rw pdf_spec ℙ volume,
    exact with_density_absolutely_continuous _ _,
    all_goals { apply_instance } },
  { intro h,
    refine ⟨⟨(measure.map X ℙ).radon_nikodym_deriv (volume : measure ℝ), _⟩⟩,
    haveI := is_finite_measure.map ℙ hX,
    rwa with_density_radon_nikodym_deriv_eq }
end

end real

end pdf

end measure_theory