import trim

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α : Type*} {m n : measurable_space α} 

namespace measure_theory

/-- The conditional expectation of an integrable function `f` on a sub-σ-algebra `m` of 
`n` is the Radon-Nikodym derivative between `(μ.with_density_signed_measure f)` restricted 
on `n` and `μ` restricted on `n`. 

Note the ordering where we take the density before the restriction. This is 
because in this case, we will only need integrability on `n` instead `m` which is a 
weaker condition (integrability requies measurabililty almost everywhere). -/
def condition_on {m n : measurable_space α} {μ : measure α} (hle : m ≤ n)
  (f : α → ℝ) (hfi : integrable f μ) : α → ℝ := 
signed_measure.radon_nikodym_deriv 
  ((μ.with_density_signed_measure f).trim hle) (μ.trim hle)

namespace condition_on

open signed_measure measure

-- possible to change to `sigma_finite`?
variables {μ : measure α} [is_finite_measure μ] {a b : ℝ} {f g : α → ℝ} (hle : m ≤ n) 
  (hfi : integrable f μ) (hgi : integrable g μ)

section

include hle hfi

lemma measurable : measurable[m] (condition_on hle f hfi) :=
measurable_radon_nikodym_deriv _ _

lemma integrable : @integrable ℝ _ _ α m (condition_on hle f hfi) (μ.trim hle) :=
integrable_radon_nikodym_deriv _ _

lemma condition_on_spec {i : set α} (hi : measurable_set[m] i) :
  ∫ x in i, condition_on hle f hfi x ∂(μ.trim hle) = ∫ x in i, f x ∂μ :=
begin
  rw [← with_density_signed_measure_trim_eq_integral hle hfi hi,
      ← signed_measure.with_density_radon_nikodym_deriv_eq
        ((μ.with_density_signed_measure f).trim hle) (μ.trim hle) _,
      ← condition_on, with_density_signed_measure_apply (integrable _ _) hi],
  { apply_instance },
  { refine vector_measure.absolutely_continuous.mk (λ j hj₁ hj₂, _),
    rw [to_ennreal_vector_measure_apply_measurable hj₁, 
        trim_measurable_set_eq hle hj₁] at hj₂,
    rw [vector_measure.trim_measurable_set_eq hle hj₁, 
        with_density_signed_measure_apply hfi (hle _ hj₁)],
    simp only [restrict_eq_zero.mpr hj₂, integral_zero_measure] }
end

end

/-- If `f` is measurable on a sub-σ-algebra `m`, then the condition of `f` on `n` is 
equal to `f` almost everywhere. -/
lemma ae_eq_of_measurable (hle : m ≤ n) (hfm : measurable[m] f) 
  (hfi : measure_theory.integrable f μ) : 
  condition_on hle f hfi =ᵐ[μ.trim hle] f :=
begin
  refine integrable.ae_eq_of_forall_set_integral_eq _ _ (integrable _ _) 
    (hfi.trim hle hfm) (λ i hi _, _),
  rw [condition_on_spec hle hfi hi, ← set_integral_trim hle hfm hi],
end

lemma ae_eq_of_measurable' (hle : m ≤ n) (hfm : measurable[m] f) 
  (hfi : measure_theory.integrable f μ) : 
  condition_on hle f hfi =ᵐ[μ] f :=
ae_eq_of_ae_eq_trim (ae_eq_of_measurable hle hfm hfi)

-- using `ae_eq_of_ae_eq_trim` we can obtain the ae eq on `μ`

section 

include hle hfi hgi

lemma add : 
  condition_on hle (f + g) (hfi.add hgi) =ᵐ[μ.trim hle] 
  condition_on hle f hfi + condition_on hle g hgi :=
begin
  refine integrable.ae_eq_of_forall_set_integral_eq _ _ (integrable _ _) 
    ((integrable _ _).add (integrable _ _)) (λ i hi _, _),
  rw [condition_on_spec hle (hfi.add hgi) hi, 
      integral_add' hfi.integrable_on hgi.integrable_on, 
      ← condition_on_spec hle hfi hi, ← condition_on_spec hle hgi hi, 
      ← integral_add'],
  { exact @integrable.integrable_on _ _ m _ _ _ _ _ (integrable hle hfi) },
  { exact @integrable.integrable_on _ _ m _ _ _ _ _ (integrable hle hgi) },
end  

end

section

include hle hfi

variable {r : ℝ}

lemma smul : 
  condition_on hle (r • f) (hfi.smul r) =ᵐ[μ.trim hle] r • condition_on hle f hfi :=
begin
  refine integrable.ae_eq_of_forall_set_integral_eq _ _ (integrable _ _) _ _,
  { convert ((integrable hle hfi).smul r) /- exact is slow -/ },
  { intros s hs _,
    erw [condition_on_spec hle _ hs, integral_smul, 
         ← condition_on_spec hle hfi hs, ← integral_smul],
    refl,
    apply_instance }
end

end

end condition_on

end measure_theory