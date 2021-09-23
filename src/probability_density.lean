/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.decomposition.radon_nikodym
import measure_theory.measure.lebesgue

/-!
# Probability density function

This file defines the probability density function of a random variable. In particular,
a measurable function `f` is said to the probability density function of a random variable `X`
if for all measurable set `S`, `ℙ(X ∈ S) = ∫ x in S, f x dx`. Probability density functions
is one way of describing the distribution of a random variable, and is useful for calculating
probabilities and finding moments (although the latter is better achieved with moment generating
functions).

This file also defines the continuous uniform distribution and proves some properties about
random variables with this distribution.

## Main definitions

* `measure_theory.measure.has_pdf` : A random variable `X : α → E` is said to `has_pdf` with
  respect to the measure `ℙ` on `α` and `μ` on `E` if there exists a measurable function `f`
  such that the push-forward measure of `ℙ` along `X` equals `μ.with_density f`.
* `measure_theory.measure.pdf` : If `X` is a random variable that `has_pdf X ℙ μ`, then `pdf X`
  is the measurable function `f` such that the push-forward measure of `ℙ` along `X` equals
  `μ.with_density f`.
* `measure_theory.measure.pdf.uniform` : A random variable `X` is said to follow the uniform
  distribution if it has a constant probability density function with a compact, non-null support.

## Main results

* `measure_theory.measure.pdf.integral_mul_eq_integral'` : Law of the unconscious statistician,
  i.e. if a random variable `X : α → E` has pdf `f`, then `𝔼(g(X)) = ∫ x, g x * f x dx` for
  all measurable `g : E → ℝ`.
* `measure_theory.measure.pdf.integral_mul_eq_integral` : A real-valued random variable `X` with
  pdf `f` has expectation `∫ x, x * f x dx`.
* `measure_theory.measure.pdf.uniform.integral_eq` : If `X` follows the uniform distribution with
  its pdf having support `s`, then `X` has expectation `(λ s)⁻¹ * ∫ x in s, x dx` where `λ`
  is the Lebesgue measure.

## TODOs

Ultimately, we would also like to define characteristic functions to describe distributions as
it exists for all random variables. However, to define this, we will need Fourier transforms
which we currently do not have.
-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal

namespace measure_theory

open topological_space

variables {α E : Type*} [normed_group E] [measurable_space E] [second_countable_topology E]
  [normed_space ℝ E] [complete_space E] [borel_space E]

section lemmas

variables {m : measurable_space α} {μ : measure α}

lemma set_lintegral_mono_ae {s : set α} {f g : α → ℝ≥0∞}
  (hf : measurable f) (hg : measurable g) (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) :
  ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
lintegral_mono_ae $ (ae_restrict_iff $ measurable_set_le hf hg).2 hfg

lemma set_lintegral_mono {s : set α} {f g : α → ℝ≥0∞}
  (hf : measurable f) (hg : measurable g) (hfg : ∀ x ∈ s, f x ≤ g x) :
  ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
set_lintegral_mono_ae hf hg (ae_of_all _ hfg)

lemma set_lintegral_lt_top_of_bdd_above
  {s : set α} (hs : μ s < ∞) {f : α → ℝ≥0} (hf : measurable f) (hbdd : bdd_above (f '' s)) :
  ∫⁻ x in s, f x ∂μ < ∞ :=
begin
  obtain ⟨M, hM⟩ := hbdd,
  rw mem_upper_bounds at hM,
  refine lt_of_le_of_lt (set_lintegral_mono hf.coe_nnreal_ennreal
    (@measurable_const _ _ _ _ ↑M) _) _,
  { simpa using hM },
  { rw lintegral_const,
    refine ennreal.mul_lt_top ennreal.coe_lt_top.ne _,
    simp [hs.ne] }
end

lemma set_lintegral_lt_top_of_is_compact [topological_space α] [opens_measurable_space α]
  {s : set α} (hs : μ s < ∞) (hsc : is_compact s) {f : α → ℝ≥0} (hf : continuous f) :
  ∫⁻ x in s, f x ∂μ < ∞ :=
set_lintegral_lt_top_of_bdd_above hs hf.measurable (hsc.image hf).bdd_above

end lemmas 

namespace measure

/-- A random variable `X : α → E` is said to `has_pdf` with respect to the measure `ℙ` on `α` and
`μ` on `E` if there exists a measurable function `f` such that the push-forward measure of `ℙ`
along `X` equals `μ.with_density f`. -/
class has_pdf {m : measurable_space α} (X : α → E)
  (ℙ : measure α) (μ : measure E . volume_tac) : Prop :=
(pdf' : ∃ (f : E → ℝ≥0∞), measurable f ∧ map X ℙ = μ.with_density f)

/-- If `X` is a random variable that `has_pdf X ℙ μ`, then `pdf X` is the measurable function `f`
such that the push-forward measure of `ℙ` along `X` equals `μ.with_density f`. -/
def pdf {m : measurable_space α} (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) :=
if hX : has_pdf X ℙ μ then classical.some hX.pdf' else 0

@[measurability]
lemma measurable_pdf {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) :
  measurable (pdf X ℙ μ) :=
begin
  by_cases hX : has_pdf X ℙ μ,
  { rw [pdf, dif_pos hX],
    exact (classical.some_spec hX.pdf').1 },
  { rw [pdf, dif_neg hX],
    exact measurable_zero }
end

lemma pdf_spec {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : has_pdf X ℙ μ] :
  measure.map X ℙ = μ.with_density (pdf X ℙ μ) :=
begin
  rw [pdf, dif_pos hX],
  exact (classical.some_spec hX.pdf').2
end

lemma pdf_spec' {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : has_pdf X ℙ μ]
  {s : set E} (hs : measurable_set s) :
  measure.map X ℙ s = ∫⁻ x in s, pdf X ℙ μ x ∂μ :=
by rw [← with_density_apply _ hs, pdf_spec X ℙ μ]

namespace pdf

variables {m : measurable_space α} {ℙ : measure α} {μ : measure E}

section

lemma lintegral_eq_measure_univ {X : α → E} [has_pdf X ℙ μ] (hX : measurable X) :
  ∫⁻ x, pdf X ℙ μ x ∂μ = ℙ set.univ :=
begin
  rw [← set_lintegral_univ, ← pdf_spec' X ℙ μ measurable_set.univ,
      measure.map_apply hX measurable_set.univ, set.preimage_univ],
end

lemma ae_lt_top {m : measurable_space α} (ℙ : measure α) [is_finite_measure ℙ] {μ : measure E}
  {X : α → E} (hX : measurable X) : ∀ᵐ x ∂μ, pdf X ℙ μ x < ∞ :=
begin
  by_cases hpdf : has_pdf X ℙ μ,
  { refine ae_lt_top (measurable_pdf X ℙ μ) _,
    rw lintegral_eq_measure_univ hX,
    { exact (measure_lt_top _ _).ne },
    { exact hpdf } },
  { rw [pdf, dif_neg hpdf],
    exact filter.eventually_of_forall (λ x, with_top.zero_lt_top) }
end

lemma of_real_to_real_ae_eq [is_finite_measure ℙ] {X : α → E} (hX : measurable X) :
  (λ x, ennreal.of_real (pdf X ℙ μ x).to_real) =ᵐ[μ] pdf X ℙ μ :=
begin
  by_cases hpdf : has_pdf X ℙ μ,
  { haveI := hpdf,
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
      convert ae_lt_top ℙ hX,
      simp_rw [lt_top_iff_ne_top] } },
  { convert ae_eq_refl _,
    ext1 x,
    rw [pdf, dif_neg hpdf, pi.zero_apply, ennreal.zero_to_real, ennreal.of_real_zero] }
end

/-- **The Law of the Unconscious Statistician**: Given a random variable `X` and a measurable
function `f`, we have `f ∘ X` is a random variable and have expectation `∫ x, f x * pdf X ∂μ`
where `μ` is a measure on the codomain of `X`. -/
lemma integral_mul_eq_integral' [is_finite_measure ℙ] {X : α → E} [has_pdf X ℙ μ]
  (hX : measurable X) (f : E → ℝ) (hf : measurable f)
  (hpdf : integrable (λ x, f x * (pdf X ℙ μ x).to_real) μ) :
  ∫ x, f x * (pdf X ℙ μ x).to_real ∂μ = ∫ x, f (X x) ∂ℙ :=
begin
  rw [← integral_map hX hf.ae_measurable, pdf_spec X ℙ μ,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part,
      lintegral_with_density_eq_lintegral_mul, lintegral_with_density_eq_lintegral_mul],
  { congr' 2,
    { have : ∀ x, ennreal.of_real (f x * (pdf X ℙ μ x).to_real) =
        ennreal.of_real (pdf X ℙ μ x).to_real * ennreal.of_real (f x),
      { intro x,
        rw [mul_comm, ennreal.of_real_mul ennreal.to_real_nonneg] },
      simp_rw [this],
      exact lintegral_congr_ae (filter.eventually_eq.mul
        (of_real_to_real_ae_eq hX) (ae_eq_refl _)) },
    { have : ∀ x, ennreal.of_real (- (f x * (pdf X ℙ μ x).to_real)) =
        ennreal.of_real (pdf X ℙ μ x).to_real * ennreal.of_real (-f x),
      { intro x,
        rw [neg_mul_eq_neg_mul, mul_comm, ennreal.of_real_mul ennreal.to_real_nonneg] },
      simp_rw [this],
      exact lintegral_congr_ae (filter.eventually_eq.mul
        (of_real_to_real_ae_eq hX) (ae_eq_refl _)) } },
  { exact measurable_pdf X ℙ μ },
  { exact (measurable.neg hf).ennreal_of_real },
  { exact measurable_pdf X ℙ μ},
  { exact measurable.ennreal_of_real hf },
  { refine ⟨hf.ae_measurable, _⟩,
    rw [has_finite_integral, lintegral_with_density_eq_lintegral_mul _
          (measurable_pdf _ _ _) hf.nnnorm.coe_nnreal_ennreal],
    have : (λ x, (pdf X ℙ μ * λ x, ↑∥f x∥₊) x) =ᵐ[μ] (λ x, ∥f x * (pdf X ℙ μ x).to_real∥₊),
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

/-- A random variable that `has_pdf` is quasi-measure preserving. -/
lemma to_quasi_measure_preserving (X : α → E) (hX : measurable X) [has_pdf X ℙ μ] :
  quasi_measure_preserving X ℙ μ :=
{ measurable := hX,
  absolutely_continuous :=
  begin
    rw pdf_spec X ℙ μ,
    exact with_density_absolutely_continuous _ _,
    all_goals { apply_instance }
  end }

lemma map_absolutely_continuous {X : α → E} (hX : measurable X) [has_pdf X ℙ μ] :
  map X ℙ ≪ μ :=
(to_quasi_measure_preserving X hX).absolutely_continuous

end

section real

variables [is_finite_measure ℙ] {X : α → ℝ} (hX : measurable X)

include hX

/-- A real-valued random variable `X` `has_pdf X ℙ λ` (where `λ` is the Lebesgue measure) if and
only if the push-forward measure of `ℙ` along `X` is absolutely continuous with respect to `λ`. -/
lemma has_pdf_iff : has_pdf X ℙ ↔ map X ℙ ≪ volume :=
begin
  split,
  { intro hX',
    exactI map_absolutely_continuous hX },
  { intro h,
    refine ⟨⟨(measure.map X ℙ).radon_nikodym_deriv volume, measurable_radon_nikodym_deriv _ _, _⟩⟩,
    haveI := ℙ.is_finite_measure_map hX,
    rwa with_density_radon_nikodym_deriv_eq }
end

/-- A real-valued random variable that `has_pdf` transformed under a `quasi_measure_preserving`
map also `has_pdf`. -/
lemma quasi_measure_preserving_has_pdf [has_pdf X ℙ]
  (g : ℝ → ℝ) (hg : quasi_measure_preserving g) :
  has_pdf (g ∘ X) ℙ :=
begin
  rw [has_pdf_iff (hg.measurable.comp hX), ← map_map hg.measurable hX, pdf_spec X ℙ],
  refine absolutely_continuous.mk (λ s hsm hs, _),
  rw [map_apply hg.measurable hsm, with_density_apply _ (hg.measurable hsm)],
  have := hg.absolutely_continuous hs,
  rw map_apply hg.measurable hsm at this,
  exact set_lintegral_measure_zero _ _ this,
  apply_instance
end

/-- If `X` is a real-valued random variable that has pdf `f`, then the expectation of `X` equals
`∫ x, x * f x ∂λ` where `λ` is the Lebesgue measure. -/
lemma integral_mul_eq_integral [has_pdf X ℙ]
  (hpdf : integrable (λ x, x * (pdf X ℙ volume x).to_real) volume) :
  ∫ x, x * (pdf X ℙ volume x).to_real ∂(volume) = ∫ x, X x ∂ℙ :=
integral_mul_eq_integral' hX _ measurable_id hpdf

lemma has_finite_integral_mul {f : ℝ → ℝ} {g : ℝ → ℝ≥0∞}
  (hg : pdf X ℙ =ᵐ[volume] g) (hgi : ∫⁻ x, ∥f x∥₊ * g x ∂(volume) < ∞) :
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

/-- A random variable `X` has uniform distribution if it has a probability density function `f`
with compact support `s` such that `f = (μ s)⁻¹ 1ₛ` a.e. where `1ₛ` is the indicator function
for `s`.

We require compact support since otherwise the expectation might not be finite. -/
class uniform {m : measurable_space α} (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac)
  extends has_pdf X ℙ μ :=
(support' : set E) (compact_support' : is_compact support')
(support_not_null' : 0 < μ support')
(uniform' : pdf X ℙ μ =ᵐ[μ] support'.indicator ((μ support')⁻¹ • 1))

namespace uniform

/-- The support of the probability density function of a random variable of uniform distribution. -/
def support {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : uniform X ℙ μ] : set E :=
hX.support'

lemma is_compact_support {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : uniform X ℙ μ] :
  is_compact (support X ℙ μ) :=
hX.compact_support'

@[measurability]
lemma measurable_set_support {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : uniform X ℙ μ] :
  measurable_set (support X ℙ μ) :=
(is_compact_support X ℙ μ).is_closed.measurable_set

lemma support_not_null {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : uniform X ℙ μ] :
  0 < μ (support X ℙ μ) :=
hX.support_not_null'

lemma pdf_ae_eq {m : measurable_space α} (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac)
  [hX : uniform X ℙ μ] :
  pdf X ℙ μ =ᵐ[μ] (support X ℙ μ).indicator ((μ (support X ℙ μ))⁻¹ • 1) :=
hX.uniform'

lemma pdf_to_real_ae_eq {m : measurable_space α}
  (X : α → E) (ℙ : measure α) (μ : measure E . volume_tac) [hX : uniform X ℙ μ] :
  (λ x, (pdf X ℙ μ x).to_real) =ᵐ[μ]
  (λ x, ((support X ℙ μ).indicator ((μ (support X ℙ μ))⁻¹ • (1 : E → ℝ≥0∞)) x).to_real) :=
filter.eventually_eq.fun_comp (pdf_ae_eq X ℙ μ) ennreal.to_real

variables [is_finite_measure ℙ] {X : α → ℝ} [uniform X ℙ volume]

lemma mul_pdf_integrable (hX : measurable X) :
  integrable (λ x : ℝ, x * (pdf X ℙ volume x).to_real) volume :=
begin
  by_cases hsupp : volume (support X ℙ) = ∞,
  { have : pdf X ℙ =ᵐ[volume] 0,
    { refine ae_eq_trans (pdf_ae_eq X ℙ) _,
      simp [hsupp] },
    refine integrable.congr (integrable_zero _ _ _) _,
    rw [(by simp : (λ x, 0 : ℝ → ℝ) = (λ x, x * (0 : ℝ≥0∞).to_real))],
    refine filter.eventually_eq.mul (ae_eq_refl _)
      (filter.eventually_eq.fun_comp this.symm ennreal.to_real) },
  refine ⟨ae_measurable_id'.mul (measurable_pdf X ℙ).ae_measurable.ennreal_to_real, _⟩,
  refine has_finite_integral_mul hX (pdf_ae_eq X ℙ) _,
  set ind := (volume (support X ℙ))⁻¹ • (1 : ℝ → ℝ≥0∞) with hind,
  have : ∀ x, ↑∥x∥₊ * (support X ℙ).indicator ind x =
    (support X ℙ).indicator (λ x, ∥x∥₊ * ind x) x :=
      λ x, ((support X ℙ).indicator_mul_right (λ x, ↑∥x∥₊) ind).symm,
  simp only [this, lintegral_indicator _ (measurable_set_support X ℙ), hind, mul_one,
             algebra.id.smul_eq_mul, pi.one_apply, pi.smul_apply],
  rw lintegral_mul_const _ measurable_nnnorm.coe_nnreal_ennreal,
  { exact ennreal.mul_lt_top (set_lintegral_lt_top_of_is_compact
      (lt_top_iff_ne_top.2 hsupp) (is_compact_support X ℙ) continuous_nnnorm).ne
      (ennreal.inv_lt_top.2 (support_not_null X ℙ)).ne },
  { apply_instance }
end

/-- A real uniform random variable `X` with support `s` has expectation
`(λ s)⁻¹ * ∫ x in s, x ∂λ` where `λ` is the Lebesgue measure. -/
lemma integral_eq (hX : measurable X) :
  ∫ x, X x ∂ℙ =
  (volume (support X ℙ))⁻¹.to_real * ∫ x in support X ℙ, x ∂(volume) :=
begin
  rw ← integral_mul_eq_integral hX (mul_pdf_integrable hX),
  all_goals { try { apply_instance } },
  rw integral_congr_ae (filter.eventually_eq.mul (ae_eq_refl _) (pdf_to_real_ae_eq X ℙ)),
  have : ∀ x, x * ((support X ℙ).indicator
      ((volume (support X ℙ))⁻¹ • (1 : ℝ → ℝ≥0∞)) x).to_real =
    x * ((support X ℙ).indicator
      ((volume (support X ℙ))⁻¹.to_real • (1 : ℝ → ℝ)) x),
  { refine λ x, congr_arg ((*) x) _,
    by_cases hx : x ∈ support X ℙ,
    { simp [set.indicator_of_mem hx] },
    { simp [set.indicator_of_not_mem hx] }},
  simp_rw [this, ← (support X ℙ).indicator_mul_right (λ x, x),
           integral_indicator (measurable_set_support X ℙ)],
  change ∫ x in support X ℙ, x * ((volume (support X ℙ))⁻¹.to_real • 1) ∂(volume) = _,
  rw [integral_mul_right, mul_comm, algebra.id.smul_eq_mul, mul_one],
end .

end uniform

end

end pdf

end measure

end measure_theory
