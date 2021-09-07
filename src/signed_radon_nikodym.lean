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

namespace signed_measure

open measure vector_measure

def radon_nikodym_deriv (s : signed_measure α) (μ : measure α) : α → ℝ := λ x,
(s.to_jordan_decomposition.pos_part.radon_nikodym_deriv μ x).to_real -
(s.to_jordan_decomposition.neg_part.radon_nikodym_deriv μ x).to_real

@[measurability]
lemma measurable_radon_nikodym_deriv (s : signed_measure α) (μ : measure α) : 
  measurable (radon_nikodym_deriv s μ) :=
begin
  rw [radon_nikodym_deriv],
  measurability,
end

lemma has_finite_integral_to_real_of_lintegral_ne_top 
  {μ : measure α} {f : α → ℝ≥0∞} (hf : ∫⁻ x, f x ∂μ ≠ ∞) :
  has_finite_integral (λ x, (f x).to_real) μ :=
begin
  have : ∀ x, (∥(f x).to_real∥₊ : ℝ≥0∞) = 
    @coe ℝ≥0 ℝ≥0∞ _ (⟨(f x).to_real, ennreal.to_real_nonneg⟩ : ℝ≥0),
  { intro x, rw real.nnnorm_of_nonneg },
  simp_rw [has_finite_integral, this],
  refine lt_of_le_of_lt (lintegral_mono (λ x, _)) (lt_top_iff_ne_top.2 hf),
  by_cases hfx : f x = ∞,
  { simp [hfx] },
  { lift f x to ℝ≥0 using hfx with fx,
    simp [← h] }
end

@[simp]
lemma lintegral_univ {μ : measure α} (f : α → ℝ≥0∞) : 
  ∫⁻ x in set.univ, f x ∂μ = ∫⁻ x, f x ∂μ :=
by rw measure.restrict_univ

-- move to `measure` namespace
lemma lintegral_radon_nikodym_deriv_lt_top 
  (μ ν : measure α) [is_finite_measure μ] : 
  ∫⁻ x, μ.radon_nikodym_deriv ν x ∂ν < ⊤ :=
begin
  by_cases hl : have_lebesgue_decomposition μ ν,
  { haveI := hl,
    obtain ⟨-, -, hadd⟩ := have_lebesgue_decomposition_spec μ ν,
    rw [← lintegral_univ, ← with_density_apply _ measurable_set.univ],
    refine lt_of_le_of_lt 
      (le_add_left (le_refl _) : _ ≤ μ.singular_part ν set.univ + 
        ν.with_density (μ.radon_nikodym_deriv ν) set.univ) _,
    rw [← measure.add_apply, ← hadd],
    exact measure_lt_top _ _ },
  { erw [measure.radon_nikodym_deriv, dif_neg hl, lintegral_zero],
    exact with_top.zero_lt_top },
end

lemma integrable_radon_nikodym_deriv (s : signed_measure α) (μ : measure α) :
  integrable (radon_nikodym_deriv s μ) μ :=
begin
  refine integrable.sub _ _;
  { split, measurability,
    exact has_finite_integral_to_real_of_lintegral_ne_top 
      (lintegral_radon_nikodym_deriv_lt_top _ μ).ne }
end .

lemma lintegral_in_const {μ : measure α} {f : α → ℝ≥0∞} (hf : measurable f) (r : ℝ≥0∞) : 
  ∫⁻ x in {x | f x = r}, f x ∂μ = r * μ {x | f x = r} :=
begin
  have : ∀ᵐ x ∂μ, x ∈ {x | f x = r} → f x = r , exact ae_of_all μ (λ _ hx, hx),
  erw [set_lintegral_congr_fun _ this, lintegral_const, 
       measure.restrict_apply measurable_set.univ, set.univ_inter],
  rw (_ : {x : α | f x = r} = f ⁻¹' {r}),
  { exact hf (set.finite.measurable_set (set.finite_singleton r)) },
  { simp_rw [set.preimage, set.mem_singleton_iff] },
end

lemma lintegral_eq_top_of_measure_eq_top_pos {μ : measure α} {f : α → ℝ≥0∞} 
  (hf : measurable f) (hμf : 0 < μ {x | f x = ∞}) : ∫⁻ x, f x ∂μ = ∞ :=
begin
  have : ∫⁻ x in {x | f x = ∞}, f x ∂μ ≤ ∫⁻ x, f x ∂μ,
  { conv_rhs { rw ← lintegral_univ },
    exact lintegral_mono_set (set.subset_univ _) },
  refine eq_top_iff.2 (le_trans _ this),
  rw [lintegral_in_const hf, ennreal.top_mul, if_neg hμf.ne.symm],
  exact le_refl _,
end

lemma eventually_le_top_of_lintegral_lt_top {μ : measure α} 
  {f : α → ℝ≥0∞} (hf : measurable f) (hμf : ∫⁻ x, f x ∂μ ≠ ∞) : ∀ᵐ x ∂μ, f x < ∞ :=
begin
  simp_rw [ae_iff, ennreal.not_lt_top],
  by_contra h,
  rw [← ne.def, ← pos_iff_ne_zero] at h,
  exact hμf (lintegral_eq_top_of_measure_eq_top_pos hf h),
end

-- move to `measure` namespace
lemma with_density_radon_nikodym_deriv_to_real_eq {μ ν : measure α} [is_finite_measure μ] 
  [have_lebesgue_decomposition μ ν] (h : μ ≪ ν) {i : set α} (hi : measurable_set i) :
  ∫ x in i, (μ.radon_nikodym_deriv ν x).to_real ∂ν = (μ i).to_real :=
begin
  rw [integral_to_real, ← with_density_apply _ hi,
      with_density_radon_nikodym_deriv_eq μ ν h],
  { measurability },
  { refine eventually_le_top_of_lintegral_lt_top (μ.measurable_radon_nikodym_deriv ν)
      (lt_of_le_of_lt (lintegral_mono_set i.subset_univ) _).ne,
    rw [← with_density_apply _ measurable_set.univ, 
        with_density_radon_nikodym_deriv_eq μ ν h],
    exact measure_lt_top _ _ },
end

lemma with_density_radon_nikodym_deriv_eq
  (s : signed_measure α) (μ : measure α) [sigma_finite μ] 
  (h : s ≪ μ.to_ennreal_vector_measure) :
  μ.with_density_signed_measure (s.radon_nikodym_deriv μ) = s :=
begin
  rw [absolutely_continuous_iff, (_ : μ.to_ennreal_vector_measure.ennreal_to_measure = μ), 
      total_variation_absolutely_continuous_iff] at h,
  { ext1 i hi,
    rw [with_density_signed_measure_apply (integrable_radon_nikodym_deriv _ _) hi, 
        radon_nikodym_deriv, integral_sub, 
        with_density_radon_nikodym_deriv_to_real_eq h.1 hi, 
        with_density_radon_nikodym_deriv_to_real_eq h.2 hi],
    { conv_rhs { rw ← s.to_signed_measure_to_jordan_decomposition },
      erw vector_measure.sub_apply,
      rw [to_signed_measure_apply_measurable hi, to_signed_measure_apply_measurable hi] },
    all_goals { rw ← integrable_on_univ,
      refine integrable_on.restrict _ measurable_set.univ,
      refine ⟨_, has_finite_integral_to_real_of_lintegral_ne_top _⟩,
      { measurability },
      { rw lintegral_univ,
        exact (lintegral_radon_nikodym_deriv_lt_top _ _).ne } } },
  { exact equiv_measure.right_inv μ }
end

end signed_measure

end measure_theory