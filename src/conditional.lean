import probability_theory.independence
import singular

/- In this file we define the conditional expectation of a random variable 
with respect to some sub-σ-algebra. -/

noncomputable theory
open_locale classical big_operators nnreal ennreal

variables {α β : Type*}

namespace measure_theory

local infix ` . `:max := measure.with_density
local notation π ` .[`:max 𝓕:max `] `:0 f := @measure.with_density _ 𝓕 π f
local notation μ ` ≪[`:max 𝓕:max `] `:0 ν := @measure.absolutely_continuous _ 𝓕 μ ν 

section

variables [measurable_space α] {μ : measure α}

lemma lintegral_in_measure_zero {s : set α} {f : α → ℝ≥0∞} (hs' : μ s = 0) : 
  ∫⁻ x in s, f x ∂μ = 0 :=
begin
  convert lintegral_zero_measure _,
  refine measure.restrict_eq_zero.2 hs',
end

lemma with_density.finite_measure [finite_measure μ] {f : α → ℝ≥0∞} 
  (hf : ∫⁻ a, f a ∂μ < ∞) : finite_measure (μ . f) := 
{ measure_univ_lt_top := 
    by rwa [with_density_apply _ measurable_set.univ, measure.restrict_univ] }

lemma with_density_add {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g) : 
  μ . (f + g) = μ . f + μ . g :=
begin
  refine measure_theory.measure.ext (λ s hs, _),
  rw [with_density_apply _ hs, measure.coe_add, pi.add_apply, 
      with_density_apply _ hs, with_density_apply _ hs, ← lintegral_add hf hg], 
  refl,
end

lemma sub_eq_zero_of_with_density_eq {f g : α → ℝ≥0∞} 
  (hf :measurable f) (hg :measurable g) (h : μ . f = μ . g) : 
  μ . (f - g) = 0 :=
begin
  refine measure_theory.measure.ext (λ s hs, _),
  rw [with_density_apply _ hs, measure.coe_zero, pi.zero_apply],
  sorry
end

lemma ae_eq_of_with_density_eq {f g : α → ℝ≥0∞} 
  (hf : measurable f) (hg : measurable g) (h : μ . f = μ . g) : 
  f =ᵐ[μ] g :=
begin
  sorry,
  -- rw [ae_eq_of_sub_ae_eq_zero hf hg, ← lintegral_eq_zero_iff, 
  --     ← lintegral_univ_eq, ← with_density_apply _ measurable_set.univ,
  --     sub_eq_zero_of_with_density_eq hf hg h, measure.coe_zero, pi.zero_apply],
  -- exact hf.sub hg,
end

end

open measure_theory.measure probability_theory

lemma measure.with_density_absolutely_continuous [measurable_space α]
  (μ : measure α) (f : α → ℝ≥0∞) : μ . f ≪ μ :=
begin
  refine absolutely_continuous.mk (λ s hs₁ hs₂, _),
  rw with_density_apply _ hs₁,
  exact lintegral_in_measure_zero hs₂
end

lemma measure.trim_absolutely_continuous {𝓕 𝓖 : measurable_space α} {μ ν : @measure α 𝓕} 
  (h : 𝓖 ≤ 𝓕) (hμν : μ ≪[𝓕] ν) : μ.trim h ≪[𝓖] ν.trim h :=
begin
  refine absolutely_continuous.mk (λ s hs₁ hs₂, _),
  rw [measure.trim, to_measure_apply _ _ hs₁, to_outer_measure_apply, 
      hμν (nonpos_iff_eq_zero.1 (hs₂ ▸ le_trim h) : ν s = 0)],
end

lemma measure.with_density_trim_absolutely_continuous
  {𝓕 𝓖 : measurable_space α} (μ : @measure α 𝓕) (h : 𝓖 ≤ 𝓕) (f : α → ℝ≥0∞) : 
  (μ .[𝓕] f).trim h ≪ μ.trim h :=
measure.trim_absolutely_continuous h $ @measure.with_density_absolutely_continuous _ 𝓕 μ f

/-- Given a real-valued random `f` variable with finite expectation, its conditional 
expectation with respect to some sub-σ-algebra `𝓖`, is a `𝓖`-random variable `g` 
such that for all `𝓖`-measurable sets `s`, `∫⁻ x in s, f x ∂π = ∫⁻ x in s, g x ∂π`. 

This definition of contional expectation allow us to define the usual notion of 
contional probability. In particular, for all events `A ∈ 𝓕`, `ℙ(A | 𝓖)` is the 
condition of `𝓖` on the indicator function on `A`; and for all random variables 
`h`, the expectation of `f` with respect to `h` is the condition of `f` on `σ(h)`. -/
def condition_on {𝓕 𝓖 : measurable_space α} (h : 𝓖 ≤ 𝓕) 
  (π : @measure α 𝓕) [@finite_measure α 𝓕 π] (f : α → ℝ≥0∞) 
  (hf₁ : @measurable _ _ 𝓕 _ f) (hf₂ : @lintegral α 𝓕 π f < ⊤) : α → ℝ≥0∞ :=
classical.some 
  (@signed_measure.exists_with_density_of_absolute_continuous _ _ 
    (π.trim h) ((π .[𝓕] f).trim h) _ 
    (@measure_theory.finite_measure_trim _ _ _ _ h $ 
      @with_density.finite_measure α 𝓕 _ _ _ hf₂)
    (measure.trim_absolutely_continuous h $ 
      @measure.with_density_absolutely_continuous α 𝓕 π f)) 

namespace condition_on

variables {𝓕 𝓖 : measurable_space α} (h : 𝓖 ≤ 𝓕) 
  (π : @measure α 𝓕) [@finite_measure α 𝓕 π] (f : α → ℝ≥0∞) 
  (hf₁ : @measurable _ _ 𝓕 _ f) (hf₂ : @lintegral α 𝓕 π f < ⊤)

lemma condition_on_measurable : measurable (condition_on h π f hf₁ hf₂) :=
(exists_prop.1 (classical.some_spec 
  (@signed_measure.exists_with_density_of_absolute_continuous _ _ 
    (π.trim h) ((π .[𝓕] f).trim h) _ 
    (@measure_theory.finite_measure_trim _ _ _ _ h $ 
      @with_density.finite_measure α 𝓕 _ _ _ hf₂)
    (measure.trim_absolutely_continuous h $ 
      @measure.with_density_absolutely_continuous α 𝓕 π f)))).1

lemma condition_on_spec : 
  (π .[𝓕] f).trim h = π.trim h . (condition_on h π f hf₁ hf₂) :=
(exists_prop.1 (classical.some_spec 
  (@signed_measure.exists_with_density_of_absolute_continuous _ _ 
    (π.trim h) ((π .[𝓕] f).trim h) _ 
    (@measure_theory.finite_measure_trim _ _ _ _ h $ 
      @with_density.finite_measure α 𝓕 _ _ _ hf₂)
    (measure.trim_absolutely_continuous h $ 
      @measure.with_density_absolutely_continuous α 𝓕 π f)))).2

instance : measurable_space ℝ≥0∞ := ennreal.measurable_space

lemma condition_on_indep 
  (hf : indep (measurable_space.comap f ennreal.measurable_space) 𝓖 (π.trim h)) :
  condition_on h π f hf₁ hf₂ =ᵐ[π.trim h] f :=
begin
  sorry,
  -- refine ae_eq_of_with_density_eq (condition_on_measurable _ _ _ hf₁ _) hf₁ _,
  -- have := condition_on_measurable h π _ hf₁ hf₂,
  -- symmetry,
  -- apply condition_on_spec,
end

end condition_on

end measure_theory
