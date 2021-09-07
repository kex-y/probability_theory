import signed_radon_nikodym

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α : Type*} {m n : measurable_space α} 

namespace measure_theory

def condition_on {m n : measurable_space α} {μ : measure α} (hle : m ≤ n)
  (f : α → ℝ) (hfm : measurable f) (hfi : integrable f μ) := 
((μ.trim hle).with_density_signed_measure f).radon_nikodym_deriv (μ.trim hle)

namespace condition_on

open signed_measure measure

variables {μ : measure α} [is_finite_measure μ] (hle : m ≤ n) {f : α → ℝ}
  (hfm : measurable f) (hfi : integrable f μ)

include hle hfm hfi

lemma measurable : measurable[m] (condition_on hle f hfm hfi) :=
measurable_radon_nikodym_deriv _ _

lemma integrable : @integrable ℝ _ _ α m (condition_on hle f hfm hfi) (μ.trim hle) :=
integrable_radon_nikodym_deriv _ _

-- lemma condition_on_spec {s : set α} (hs : measurable_set[m] s) : 
--   ∫ x in s, condition_on hle f hfm hfi x ∂(μ.trim hle) = ∫ x in s, f x ∂(μ.trim hle) :=
-- begin
--   rw [← with_density_signed_measure_apply (integrable hle hfm hfi) hs, 
--       condition_on, signed_measure.with_density_radon_nikodym_deriv_eq, 
--       with_density_signed_measure_apply _ hs],
--   refine integrable.trim _ hfi hfm,
-- end

end condition_on

end measure_theory