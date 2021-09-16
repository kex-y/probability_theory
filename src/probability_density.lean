import signed_radon_nikodym
import measure_theory.measure.lebesgue

noncomputable theory
open_locale classical measure_theory nnreal ennreal

section

open measure_theory measure_theory.measure

variables {α β : Type*} [measurable_space α] [measurable_space β] 

-- PRed
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
(pdf' : ∃ (f : E → ℝ≥0∞), measurable f ∧ map X ℙ = μ.with_density f)

-- remove `has_pdf` requirement and define it as a ite statement 
def pdf (X : α → E) (ℙ : measure α) (μ : measure E) [hX : has_pdf X ℙ μ] : E → ℝ≥0∞ := 
classical.some hX.pdf'

@[measurability]
lemma measurable_pdf (X : α → E) (ℙ : measure α) (μ : measure E) [hX : has_pdf X ℙ μ] : 
  measurable (pdf X ℙ μ) :=
(classical.some_spec hX.pdf').1

lemma pdf_spec (X : α → E) (ℙ : measure α) (μ : measure E) [hX : has_pdf X ℙ μ] :
  measure.map X ℙ = μ.with_density (pdf X ℙ μ) :=
(classical.some_spec hX.pdf').2

lemma pdf_spec' (X : α → E) (ℙ : measure α) (μ : measure E) 
  [hX : has_pdf X ℙ μ] {s : set E} (hs : measurable_set s) :
  measure.map X ℙ s = ∫⁻ x in s, pdf X ℙ μ x ∂μ := 
by rw [← with_density_apply _ hs, pdf_spec X ℙ μ]

namespace pdf

variables {ℙ : measure α} {μ : measure E}

section 

variables [is_finite_measure ℙ] {X : α → E} [has_pdf X ℙ μ] (hX : measurable X)

include hX

lemma lintegral_eq_measure_univ : ∫⁻ x, pdf X ℙ μ x ∂μ = ℙ set.univ :=
begin
  rw [← set_lintegral_univ, ← pdf_spec' X ℙ μ measurable_set.univ, 
      measure.map_apply hX measurable_set.univ, set.preimage_univ],
end

lemma ae_lt_top (ℙ : measure α) [is_finite_measure ℙ] (μ : measure E) 
  {X : α → E} [has_pdf X ℙ μ] (hX : measurable X) : 
  ∀ᵐ x ∂μ, pdf X ℙ μ x < ∞ :=
begin
  refine ae_lt_top (measurable_pdf X ℙ μ) _,
  rw lintegral_eq_measure_univ hX,
  exact measure_lt_top _ _,
  apply_instance
end

lemma of_real_to_real_ae_eq : 
  (λ x, ennreal.of_real (pdf X ℙ μ x).to_real) =ᵐ[μ] pdf X ℙ μ := 
begin
  change μ {x : E | ennreal.of_real (pdf X ℙ μ x).to_real ≠ pdf X ℙ μ x} = 0,
  have : ∀ x, ennreal.of_real (pdf X ℙ μ x).to_real ≠ pdf X ℙ μ x ↔
    pdf X ℙ μ x = ∞,
  { intro x, split; intro h,
    { by_contra htop,
      rw [← ne.def, ← lt_top_iff_ne_top] at htop,
      exact h (ennreal.of_real_to_real htop.ne) },
    { rw h, simp } },
  { simp_rw this, 
    suffices hne : ∀ᵐ x ∂μ, pdf X ℙ μ x ≠ ∞,
    { simp_rw [ae_iff, not_not] at hne, exact hne },
    convert ae_lt_top ℙ μ hX,
    simp_rw [lt_top_iff_ne_top] }
end

end 

section real

variables [is_finite_measure ℙ] {X : α → ℝ} (hX : measurable X)

include hX

lemma has_pdf_iff : has_pdf X ℙ ↔ measure.map X ℙ ≪ (volume : measure ℝ) := 
begin
  split,
  { introI hX,
    rw pdf_spec X ℙ volume,
    exact with_density_absolutely_continuous _ _,
    all_goals { apply_instance } },
  { intro h,
    refine ⟨⟨(measure.map X ℙ).radon_nikodym_deriv (volume : measure ℝ), 
             measurable_radon_nikodym_deriv _ _, _⟩⟩,
    haveI := is_finite_measure.map ℙ hX,
    rwa with_density_radon_nikodym_deriv_eq }
end

/-- If `X` is a random variable that has pdf `f`, then the expectation of `X` equals 
`∫ x, x * f x ∂λ` where `λ` is the Lebesgue measure. -/
lemma lintegral_mul_eq_integral [has_pdf X ℙ volume] 
  (hpdf : integrable (λ x, x * (pdf X ℙ volume x).to_real) volume) /- finite expectation -/ : 
  ∫ x, x * (pdf X ℙ volume x).to_real ∂(volume : measure ℝ) = ∫ x, X x ∂ℙ :=
begin
  change _ = ∫ x, id (X x) ∂ℙ,
  rw [← integral_map hX ae_measurable_id, pdf_spec X ℙ volume, 
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
      lintegral_with_density_eq_lintegral_mul, lintegral_with_density_eq_lintegral_mul],
  { congr' 2,
    { have : ∀ x, ennreal.of_real (x * (pdf X ℙ volume x).to_real) = 
        ennreal.of_real (pdf X ℙ volume x).to_real * ennreal.of_real x,
      { intro x, 
        rw [mul_comm, ennreal.of_real_mul ennreal.to_real_nonneg] },
      simp_rw [this],
      exact lintegral_congr_ae (filter.eventually_eq.mul 
        (of_real_to_real_ae_eq hX) (ae_eq_refl _)) },
    { have : ∀ x, ennreal.of_real (- (x * (pdf X ℙ volume x).to_real)) = 
        ennreal.of_real (pdf X ℙ volume x).to_real * ennreal.of_real (-x),
      { intro x,
        rw [neg_mul_eq_neg_mul, mul_comm, ennreal.of_real_mul ennreal.to_real_nonneg] },
      simp_rw [this],
      exact lintegral_congr_ae (filter.eventually_eq.mul 
        (of_real_to_real_ae_eq hX) (ae_eq_refl _)) } },
  { exact measurable_pdf X ℙ volume},
  { exact measurable_id.neg.ennreal_of_real},
  { exact measurable_pdf X ℙ volume},
  { exact measurable_id.ennreal_of_real },
  { refine ⟨ae_measurable_id, _⟩,
    rw [has_finite_integral, lintegral_with_density_eq_lintegral_mul _ 
          (measurable_pdf _ _ _) measurable_id.nnnorm.coe_nnreal_ennreal],
    have : (λ x, (pdf X ℙ volume * λ x, ↑∥id x∥₊) x) =ᵐ[volume] 
      (λ x, ∥x * (pdf X ℙ volume x).to_real∥₊),
    { simp_rw [← smul_eq_mul, nnnorm_smul, ennreal.coe_mul],
      rw [smul_eq_mul, mul_comm],
      refine filter.eventually_eq.mul (ae_eq_refl _) 
        (ae_eq_trans (of_real_to_real_ae_eq hX).symm _),
      convert ae_eq_refl _,
      ext1 x,
      exact real.ennnorm_eq_of_real ennreal.to_real_nonneg },
    rw lintegral_congr_ae this,
    exact hpdf.2, 
    apply_instance },
  { assumption }
end

end real

section uniform

class uniform (X : α → E) (ℙ : measure α . volume_tac) (μ : measure E . volume_tac) (s : set E) 
  extends has_pdf X ℙ μ :=
(uniform : pdf X ℙ μ =ᵐ[μ] s.indicator ((μ s)⁻¹ • 1))

variables {X : α → E} {s : set E} [uniform X ℙ μ s]

end uniform

end pdf

end measure_theory