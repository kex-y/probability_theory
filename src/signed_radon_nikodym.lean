import measure_theory.decomposition.radon_nikodym
import measure_theory.integral.set_integral
import measure_theory.function.ae_eq_of_integral

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

lemma vector_measure.absolutely_continuous.zero {M N : Type*}
  [add_comm_monoid M] [topological_space M] [add_comm_monoid N] [topological_space N]
  (v : vector_measure α N) : (0 : vector_measure α M) ≪ v :=
λ s _, vector_measure.zero_apply s

namespace measure

open topological_space

section with_density_signed_measure

/- Show s ↦ ∫ x in s, f x ∂μ form a signed measure. -/

variables {μ ν : measure α} {f g : α → ℝ}

lemma is_finite_measure_of_real_of_integrable (hf : integrable f μ) :
  is_finite_measure (μ.with_density (λ x, ennreal.of_real (f x))) :=
is_finite_measure_with_density 
  (lt_of_le_of_lt (lintegral_mono (λ x, ennreal.of_real_le_norm (f x))) hf.2)

/-- Given a measure `μ` and a integrable function `f`, `μ.with_density_signed_measure f` is 
the signed measure which maps the set `s` to `∫ₛ f⁺ ∂μ - ∫ₛ f⁻ ∂μ`. -/
def with_density_signed_measure {m : measurable_space α} 
  (μ : measure α) (f : α → ℝ) : signed_measure α :=
if hf : integrable f μ then
@to_signed_measure α m (μ.with_density (λ x, ennreal.of_real (f x)))
(is_finite_measure_of_real_of_integrable hf)
-
@to_signed_measure α m (μ.with_density (λ x, ennreal.of_real (-f x)))
(is_finite_measure_of_real_of_integrable (integrable_neg_iff.2 hf))
else 0

lemma with_density_signed_measure_apply (hf : integrable f μ) 
  {i : set α} (hi : measurable_set i) : 
  μ.with_density_signed_measure f i = ∫ x in i, f x ∂μ :=
begin
  rw integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
  { rw [with_density_signed_measure, dif_pos hf],
    simp [if_pos hi, with_density_apply _ hi] },
  { rw ← integrable_on_univ,
    exact hf.integrable_on.restrict measurable_set.univ },
end

@[simp]
lemma with_density_signed_measure_zero : 
  μ.with_density_signed_measure 0 = 0 :=
begin
  ext1 i hi,
  erw [with_density_signed_measure_apply (integrable_zero α ℝ μ) hi],
  simp,
end

@[simp]
lemma with_density_signed_measure_neg (hf : integrable f μ) : 
  μ.with_density_signed_measure (-f) = -μ.with_density_signed_measure f :=
begin
  ext1 i hi,
  rw [vector_measure.neg_apply, with_density_signed_measure_apply hf hi, 
      ← integral_neg, with_density_signed_measure_apply hf.neg hi],
  refl
end

@[simp]
lemma with_density_signed_measure_add (hf : integrable f μ) (hg : integrable g μ) :
  μ.with_density_signed_measure (f + g) = 
  μ.with_density_signed_measure f + μ.with_density_signed_measure g :=
begin
  ext1 i hi,
  rw [with_density_signed_measure_apply (hf.add hg) hi, vector_measure.add_apply, 
      with_density_signed_measure_apply hf hi, with_density_signed_measure_apply hg hi],
  simp_rw [pi.add_apply],
  rw integral_add; rw ← integrable_on_univ,
  { exact hf.integrable_on.restrict measurable_set.univ },
  { exact hg.integrable_on.restrict measurable_set.univ }
end

@[simp]
lemma with_density_signed_measure_sub (hf : integrable f μ) (hg : integrable g μ) :
  μ.with_density_signed_measure (f - g) = 
  μ.with_density_signed_measure f - μ.with_density_signed_measure g :=
by rw [sub_eq_add_neg, sub_eq_add_neg, with_density_signed_measure_add hf hg.neg, 
       with_density_signed_measure_neg hg]

@[simp]
lemma with_density_signed_measure_smul (r : ℝ) (hf : integrable f μ) :
  μ.with_density_signed_measure (r • f) = r • μ.with_density_signed_measure f :=
begin
  ext1 i hi,
  rw [with_density_signed_measure_apply (hf.smul r) hi, vector_measure.smul_apply, 
      with_density_signed_measure_apply hf hi, ← integral_smul],
  refl
end

lemma with_density_signed_measure_absolutely_continuous 
  (μ : measure α) (f : α → ℝ) : 
  μ.with_density_signed_measure f ≪ μ.to_ennreal_vector_measure :=
begin
  by_cases hf : integrable f μ,
  { refine vector_measure.absolutely_continuous.mk (λ i hi₁ hi₂, _),
    rw to_ennreal_vector_measure_apply_measurable hi₁ at hi₂,
    rw [with_density_signed_measure_apply hf hi₁, measure.restrict_zero_set hi₂, 
        integral_zero_measure] },
  { rw [with_density_signed_measure, dif_neg hf],
    exact vector_measure.absolutely_continuous.zero _ }
end

end with_density_signed_measure

section

variables {μ : measure α} {f g : α → ℝ}

/-- Having the same density implies the underlying functions are equal almost everywhere. -/
lemma ae_eq_of_with_density_signed_measure_eq (hf : integrable f μ) (hg : integrable g μ) 
  (hfg : μ.with_density_signed_measure f = μ.with_density_signed_measure g) :
  f =ᵐ[μ] g :=
begin
  refine integrable.ae_eq_of_forall_set_integral_eq f g hf hg (λ i hi _, _),
  rw [← with_density_signed_measure_apply hf hi, hfg, with_density_signed_measure_apply hg hi]
end

end

end measure

end measure_theory