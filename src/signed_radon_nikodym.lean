import measure_theory.decomposition.radon_nikodym
import measure_theory.integral.set_integral
import 

noncomputable theory
open_locale classical measure_theory nnreal ennreal

lemma ennreal.of_real_le_norm (r : ℝ) : ennreal.of_real r ≤ ∥r∥₊ :=
begin
  by_cases hr : r ≤ 0,
  { rw [ennreal.of_real_eq_zero.2 hr],
    simp only [zero_le', ennreal.coe_nonneg] },
  { rw [real.nnnorm_of_nonneg (le_of_not_le hr), ennreal.of_real, ennreal.coe_le_coe, 
        ← nnreal.coe_le_coe, real.coe_to_nnreal r (le_of_not_le hr), subtype.coe_mk] }
end

variables {α β : Type*} {m : measurable_space α}

namespace measure_theory

include m

namespace measure

open topological_space

section with_density'

/- Show s ↦ ∫ x in s, f x ∂μ form a signed measure. -/

variables {μ ν : measure α} [is_finite_measure μ] {f : α → ℝ}

lemma is_finite_measure_of_real_of_integrable (hf : integrable f μ) :
  is_finite_measure (μ.with_density (λ x, ennreal.of_real (f x))) :=
is_finite_measure_with_density 
  (lt_of_le_of_lt (lintegral_mono (λ x, ennreal.of_real_le_norm (f x))) hf.2)

/-- Given a measure `μ` and a integrable function `f`, `μ.with_density_signed_measure f` is 
the signed measure which maps the set `s` to `∫ₛ f⁺ ∂μ - ∫ₛ f⁻ ∂μ`. -/
def with_density_signed_measure {m : measurable_space α} 
  (μ : measure α) [is_finite_measure μ] (f : α → ℝ) : signed_measure α :=
if hf : integrable f μ then
@to_signed_measure α m (μ.with_density (λ x, ennreal.of_real (f x)))
(is_finite_measure_of_real_of_integrable hf)
-
@to_signed_measure α m (μ.with_density (λ x, ennreal.of_real (-f x)))
(is_finite_measure_of_real_of_integrable (integrable_neg_iff.2 hf))
else 0

lemma with_density_signed_measure_apply (hf : integrable f μ) 
  (i : set α) (hi : measurable_set i) : 
  μ.with_density_signed_measure f i = ∫ x in i, f x ∂μ :=
begin
  rw integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
  { rw [with_density_signed_measure, dif_pos hf],
    simp [if_pos hi, with_density_apply _ hi] },
  { rw [← integrable_on_univ],
    exact integrable_on.restrict hf.integrable_on measurable_set.univ },
end

end with_density'

end measure

end measure_theory
