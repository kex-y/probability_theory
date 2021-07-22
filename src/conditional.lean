import probability_theory.independence
import singular

/- In this file we define the conditional expectation of a random variable 
with respect to some sub-σ-algebra. -/

noncomputable theory
open_locale classical big_operators nnreal ennreal

variables {α β : Type*}

namespace measure_theory

local infix ` . `:max := measure.with_density

section

variables [measurable_space α] {μ : measure α}

lemma lintegral_in_measure_zero {s : set α} {f : α → ℝ≥0∞} (hs' : μ s = 0) : 
  ∫⁻ x in s, f x ∂μ = 0 :=
begin
  convert lintegral_zero_measure _,
  refine measure.restrict_eq_zero.2 hs',
end

lemma finite_measure.with_density [finite_measure μ] {f : α → ℝ≥0∞} 
  (hf : ∫⁻ a, f a ∂μ < ⊤) : finite_measure (μ . f) := 
{ measure_univ_lt_top := 
    by rwa [with_density_apply _ measurable_set.univ, measure.restrict_univ] }

end

open measure_theory.measure probability_theory

lemma measure.trim_absolutely_continuous_with_density
  {𝓕 𝓖 : measurable_space α} (μ : @measure α 𝓕) (h : 𝓖 ≤ 𝓕) (f : α → ℝ≥0∞) : 
  (μ.trim h) . f ≪ μ.trim h :=
begin
  refine absolutely_continuous.mk (λ s hs₁ hs₂, _),
  rw with_density_apply _ hs₁,
  exact lintegral_in_measure_zero hs₂
end

/-- Given a real-valued random `f` variable with finite expectation, its conditional 
expectation with respect to some sub-σ-algebra `𝓖`, is a `𝓖`-random variable `g` 
such that for all `𝓖`-measurable sets `s`, `∫⁻ x in s, f x ∂π = ∫⁻ x in s, g x ∂π`. 

This definition of contional expectation allow us to define the usual notion of 
contional probability. In particular, for all events `A ∈ 𝓕`, `ℙ(A | 𝓖)` is the 
condition of `𝓖` on the indicator function on `A`; and for all random variables 
`h`, the expectation of `f` with respect to `h` is the condition of `f` on `σ(h)`. -/
def condition_on {𝓕 𝓖 : measurable_space α} (h : 𝓖 ≤ 𝓕) 
  (π : @measure α 𝓕) [@finite_measure α 𝓕 π] (f : α → ℝ≥0∞) 
  (hf₁ : measurable f) (hf₂ : @lintegral α 𝓕 π f < ⊤) : α → ℝ≥0∞ :=
classical.some 
  (@signed_measure.exists_with_density_of_absolute_continuous _ _ 
    (π.trim h) (π.trim h . f) _ 
    (finite_measure.with_density ((@lintegral_trim _ _ _ π h _ hf₁).symm ▸ hf₂))
    (π.trim_absolutely_continuous_with_density h f)) 

namespace condition_on

variables {𝓕 𝓖 : measurable_space α} (h : 𝓖 ≤ 𝓕) 
  (π : @measure α 𝓕) [@finite_measure α 𝓕 π] (f : α → ℝ≥0∞) 
  (hf₁ : measurable f) (hf₂ : @lintegral α 𝓕 π f < ⊤)

lemma condition_on_measurable : measurable (condition_on h π f hf₁ hf₂) :=
(exists_prop.1 (classical.some_spec 
  (@signed_measure.exists_with_density_of_absolute_continuous _ _ (π.trim h)
  ((π.trim h) . f) _ 
  (finite_measure.with_density ((@lintegral_trim _ _ _ π h _ hf₁).symm ▸ hf₂))
  (π.trim_absolutely_continuous_with_density h f)))).1

lemma condition_on_spec : 
  π.trim h . f = π.trim h . (condition_on h π f hf₁ hf₂) :=
(exists_prop.1 (classical.some_spec 
  (@signed_measure.exists_with_density_of_absolute_continuous _ _ (π.trim h)
  ((π.trim h) . f) _ 
  (finite_measure.with_density ((@lintegral_trim _ _ _ π h _ hf₁).symm ▸ hf₂))
  (π.trim_absolutely_continuous_with_density h f)))).2

instance : measurable_space ℝ≥0∞ := ennreal.measurable_space

lemma condition_on_indep 
  (hf : indep (measurable_space.comap f ennreal.measurable_space) 𝓖 (π.trim h)) :
  condition_on h π f hf₁ hf₂ = f :=
begin
  -- Need uniquness of the Radon-Nikodym theorem.
  sorry
end

end condition_on

end measure_theory
