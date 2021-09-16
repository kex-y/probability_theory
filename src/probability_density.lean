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

/-- **The Law of the Unconscious Statistician**: Given a random variable `X` and a measurable 
function `f`, we have `f ∘ X` is a random variable and have expectation `∫ x, f x * pdf X ∂λ` 
where `λ` is the Lebesgue measure. -/
lemma lintegral_mul_eq_integral' [has_pdf X ℙ volume] {f : ℝ → ℝ} (hf : measurable f)
  (hpdf : integrable (λ x, f x * (pdf X ℙ volume x).to_real) volume) : 
  ∫ x, f x * (pdf X ℙ volume x).to_real ∂(volume : measure ℝ) = ∫ x, f (X x) ∂ℙ :=
begin
  rw [← integral_map hX hf.ae_measurable, pdf_spec X ℙ volume, 
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
      lintegral_with_density_eq_lintegral_mul, lintegral_with_density_eq_lintegral_mul],
  { congr' 2,
    { have : ∀ x, ennreal.of_real (f x * (pdf X ℙ volume x).to_real) = 
        ennreal.of_real (pdf X ℙ volume x).to_real * ennreal.of_real (f x),
      { intro x, 
        rw [mul_comm, ennreal.of_real_mul ennreal.to_real_nonneg] },
      simp_rw [this],
      exact lintegral_congr_ae (filter.eventually_eq.mul 
        (of_real_to_real_ae_eq hX) (ae_eq_refl _)) },
    { have : ∀ x, ennreal.of_real (- (f x * (pdf X ℙ volume x).to_real)) = 
        ennreal.of_real (pdf X ℙ volume x).to_real * ennreal.of_real (-f x),
      { intro x,
        rw [neg_mul_eq_neg_mul, mul_comm, ennreal.of_real_mul ennreal.to_real_nonneg] },
      simp_rw [this],
      exact lintegral_congr_ae (filter.eventually_eq.mul 
        (of_real_to_real_ae_eq hX) (ae_eq_refl _)) } },
  { exact measurable_pdf X ℙ volume },
  { exact (measurable.neg hf).ennreal_of_real },
  { exact measurable_pdf X ℙ volume},
  { exact measurable.ennreal_of_real hf },
  { refine ⟨hf.ae_measurable, _⟩,
    rw [has_finite_integral, lintegral_with_density_eq_lintegral_mul _ 
          (measurable_pdf _ _ _) hf.nnnorm.coe_nnreal_ennreal],
    have : (λ x, (pdf X ℙ volume * λ x, ↑∥f x∥₊) x) =ᵐ[volume] 
      (λ x, ∥f x * (pdf X ℙ volume x).to_real∥₊),
    { simp_rw [← smul_eq_mul, nnnorm_smul, ennreal.coe_mul],
      rw [smul_eq_mul, mul_comm],
      refine filter.eventually_eq.mul (ae_eq_refl _) 
        (ae_eq_trans (of_real_to_real_ae_eq hX).symm _),
      convert ae_eq_refl _,
      ext1 x,
      exact real.ennnorm_eq_of_real ennreal.to_real_nonneg },
    rw lintegral_congr_ae this,
    exact hpdf.2 },
  { assumption },
end

/-- If `X` is a random variable that has pdf `f`, then the expectation of `X` equals 
`∫ x, x * f x ∂λ` where `λ` is the Lebesgue measure. -/
lemma lintegral_mul_eq_integral [has_pdf X ℙ volume] 
  (hpdf : integrable (λ x, x * (pdf X ℙ volume x).to_real) volume) /- finite expectation -/ : 
  ∫ x, x * (pdf X ℙ volume x).to_real ∂(volume : measure ℝ) = ∫ x, X x ∂ℙ :=
lintegral_mul_eq_integral' hX measurable_id hpdf

lemma has_finite_integral_mul [has_pdf X ℙ volume] {f : ℝ → ℝ} (hf : measurable f)
  {g : ℝ → ℝ≥0∞} (hg : pdf X ℙ volume =ᵐ[volume] g) (hgi : ∫⁻ x, ∥f x∥₊ * g x ∂(volume) < ∞) : 
  has_finite_integral (λ x, f x * (pdf X ℙ volume x).to_real) volume :=
begin
  rw [has_finite_integral],
  have : (λ x, ↑∥f x∥₊ * g x) =ᵐ[volume] (λ x, ∥f x * (pdf X ℙ volume x).to_real∥₊),
  { refine ae_eq_trans (filter.eventually_eq.mul (ae_eq_refl (λ x, ∥f x∥₊)) 
      (ae_eq_trans hg.symm (of_real_to_real_ae_eq hX).symm)) _,
    simp_rw [← smul_eq_mul, nnnorm_smul, ennreal.coe_mul, smul_eq_mul],
    refine filter.eventually_eq.mul (ae_eq_refl _) _,
    convert ae_eq_refl _,
    ext1 x,
    exact real.ennnorm_eq_of_real ennreal.to_real_nonneg },
  rwa ← lintegral_congr_ae this,
end

end real

section

/-! **Uniform Distribution** -/

class uniform (X : α → E) (ℙ : measure α . volume_tac) (μ : measure E . volume_tac)  
  extends has_pdf X ℙ μ :=
(support' : set E) (measurable' : measurable_set support')
(finite_support' : μ support' < ∞)
(support_not_null' : 0 < μ support')
(uniform' : pdf X ℙ μ =ᵐ[μ] support'.indicator ((μ support')⁻¹ • 1))

namespace uniform

def support (X : α → E) (ℙ : measure α . volume_tac) (μ : measure E . volume_tac) 
  [hX : uniform X ℙ μ] : set E := 
hX.support'

@[measurability]
lemma measurable_set_support  (X : α → E) (ℙ : measure α . volume_tac) (μ : measure E . volume_tac) 
  [hX : uniform X ℙ μ] : measurable_set (support X ℙ μ) := 
hX.measurable'

lemma finite_support (X : α → E) (ℙ : measure α . volume_tac) (μ : measure E . volume_tac)
  [hX : uniform X ℙ μ] : μ (support X ℙ μ) < ∞ := 
hX.finite_support'

lemma support_not_null (X : α → E) (ℙ : measure α . volume_tac) (μ : measure E . volume_tac)
  [hX : uniform X ℙ μ] : 0 < μ (support X ℙ μ) := 
hX.support_not_null'

lemma pdf_ae_eq (X : α → E) (ℙ : measure α . volume_tac) (μ : measure E . volume_tac) 
  [hX : uniform X ℙ μ] : 
  pdf X ℙ μ =ᵐ[μ] (support X ℙ μ).indicator ((μ (support X ℙ μ))⁻¹ • 1) := 
hX.uniform'

variables [is_finite_measure ℙ] {X : α → ℝ} [uniform X ℙ volume] 

-- Is this true? 
lemma set_lintegral_nnnorm_lt_top {s : set E} (hs : μ s < ∞) : 
  ∫⁻ x in s, ∥x∥₊ ∂μ < ∞ :=
begin
  sorry
end

lemma mul_pdf_integrable (hX : measurable X) : 
  integrable (λ x : ℝ, x * (pdf X ℙ volume x).to_real) volume :=
begin
  refine ⟨ae_measurable_id'.mul (measurable_pdf X ℙ volume).ae_measurable.ennreal_to_real, _⟩,
  refine has_finite_integral_mul hX measurable_id (pdf_ae_eq X ℙ volume) _,
  set ind := (volume (support X ℙ volume))⁻¹ • (1 : ℝ → ℝ≥0∞) with hind,
  have : ∀ x, ↑∥x∥₊ * (support X ℙ volume).indicator ind x = 
    (support X ℙ volume).indicator (λ x, ∥x∥₊ * ind x) x := 
      λ x, ((support X ℙ volume).indicator_mul_right (λ x, ↑∥x∥₊) ind).symm,
  simp only [this, lintegral_indicator _ (measurable_set_support X ℙ volume), hind, mul_one, 
             algebra.id.smul_eq_mul, pi.one_apply, pi.smul_apply],
  rw lintegral_mul_const _ measurable_nnnorm.coe_nnreal_ennreal,
  { exact ennreal.mul_lt_top (set_lintegral_nnnorm_lt_top (finite_support X ℙ volume)) 
      (ennreal.inv_lt_top.2 (support_not_null X ℙ volume)) },
  { apply_instance }
end

end uniform

end

end pdf

end measure_theory