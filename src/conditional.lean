import probability_theory.independence
import singular

/- In this file we define the conditional expectation of a random variable 
with respect to some sub-σ-algebra. -/

noncomputable theory
open_locale classical big_operators nnreal ennreal

variables {α β : Type*}

namespace measure_theory

local infix ` . `:max := measure.with_density

local notation π ` .[`:25 𝓕:25 `] `:0 f := @measure.with_density _ 𝓕 π f
local notation μ ` ≪[`:25 𝓕:25 `] `:0 ν := @measure.absolutely_continuous _ 𝓕 μ ν 

local notation `∫⁻[`:25 𝓕:25 `]` binders `, ` r:(scoped:60 f, f) ` ∂` μ:70 := 
  @lintegral _ 𝓕 μ r
local notation `∫⁻[`:25 𝓕:25 `]` binders ` in ` s `, ` r:(scoped:60 f, f) ` ∂` μ:70 :=
  @lintegral _ 𝓕 (@measure.restrict _ 𝓕 μ s) r

section

variables [measurable_space α] {μ : measure α}

-- PRed
lemma lintegral_in_measure_zero {s : set α} {f : α → ℝ≥0∞} (hs' : μ s = 0) : 
  ∫⁻ x in s, f x ∂μ = 0 :=
begin
  convert lintegral_zero_measure _,
  refine measure.restrict_eq_zero.2 hs',
end

-- PRed
lemma with_density.finite_measure [finite_measure μ] {f : α → ℝ≥0∞} 
  (hf : ∫⁻ a, f a ∂μ < ∞) : finite_measure (μ . f) := 
{ measure_univ_lt_top := 
    by rwa [with_density_apply _ measurable_set.univ, measure.restrict_univ] }

lemma lintegral_add_lt_top {f g : α → ℝ≥0∞} (hf₁ : measurable f) (hg₁ : measurable g)
  (hf₂ : ∫⁻ a, f a ∂μ < ∞) (hg₂ : ∫⁻ a, g a ∂μ < ∞) : ∫⁻ a, f a + g a ∂μ < ∞ :=
begin
  rw lintegral_add hf₁ hg₁,
  exact ennreal.add_lt_top.2 ⟨hf₂, hg₂⟩,
end

-- PRed
lemma with_density_add {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g) : 
  μ . (f + g) = μ . f + μ . g :=
begin
  refine measure_theory.measure.ext (λ s hs, _),
  rw [with_density_apply _ hs, measure.coe_add, pi.add_apply, 
      with_density_apply _ hs, with_density_apply _ hs, ← lintegral_add hf hg], 
  refl,
end

lemma ae_eq_of_with_density_eq {f g : α → ℝ≥0∞} 
  (hf : measurable f) (hg : measurable g) (h : μ . f = μ . g) : 
  f =ᵐ[μ] g :=
begin
  sorry,
end

section

variables {𝓕 𝓖 : measurable_space α} (h : 𝓖 ≤ 𝓕) {π : @measure α 𝓕}

lemma trim_restrict_eq {s : set α} (hs : measurable_set s) : 
  (@measure.restrict α 𝓕 π s).trim h = (π.trim h).restrict s := 
begin
  refine measure.ext (λ t ht, _),
  rw [trim_measurable_set_eq _ ht, measure.restrict_apply ht, 
      trim_measurable_set_eq _ (ht.inter hs), measure.restrict_apply],
  exact h _ ht,
end

-- Note `f` is measurable w.r.t. to `𝓖` (which is stronger than measurable w.r.t. to `𝓕`).
lemma lintegral_in_trim {f : α → ℝ≥0∞} (hf : measurable f) 
  {s : set α} (hs : measurable_set s) : 
  ∫⁻ x in s, f x ∂(π.trim h) = ∫⁻[𝓕] x in s, f x ∂π :=
by rw [← trim_restrict_eq h hs, lintegral_trim h hf]

-- same here
lemma trim_with_density_eq {f : α → ℝ≥0∞} (hf : measurable f) :
  (π.trim h) . f = (π .[𝓕] f).trim h :=
begin
  refine measure.ext (λ s hs, _),
  rw [with_density_apply _ hs, trim_measurable_set_eq _ hs, 
      lintegral_in_trim h hf hs, with_density_apply],
  exact h _ hs,
end

end

end

open measure_theory.measure probability_theory

-- PRed
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

/- 
Perhaps it would make more sense to define conditional probability using `fact`. 

I am worried that when applying lemmas such as `condition_on_add`, Lean will find 
two different proofs for the arguments, and so won't be able to apply. 
-/

/-- Given a real-valued random `f` variable with finite expectation, its conditional 
expectation with respect to some sub-σ-algebra `𝓖`, is a `𝓖`-random variable `g` 
such that for all `𝓖`-measurable sets `s`, `∫⁻ x in s, f x ∂π = ∫⁻ x in s, g x ∂π`. 

This definition of contional expectation allow us to define the usual notion of 
contional probability. In particular, for all events `A ∈ 𝓕`, `𝔼(A | 𝓖)` is the 
condition of `𝓖` on the indicator function on `A`; and for all random variables 
`h`, the expectation of `f` with respect to `h` is the condition of `f` on `σ(h)`. -/
def condition_on {𝓕 𝓖 : measurable_space α} (h : 𝓖 ≤ 𝓕) 
  (π : @measure α 𝓕) [@finite_measure α 𝓕 π] (f : α → ℝ≥0∞) 
  (hf₁ : @measurable _ _ 𝓕 _ f) (hf₂ : ∫⁻[𝓕] x, f x ∂π < ∞) : α → ℝ≥0∞ :=
classical.some 
  (@signed_measure.exists_with_density_of_absolute_continuous _ _ 
    (π.trim h) ((π .[𝓕] f).trim h) _ 
    (@measure_theory.finite_measure_trim _ _ _ _ h $ 
      @with_density.finite_measure α 𝓕 _ _ _ hf₂)
    (measure.trim_absolutely_continuous h $ 
      @measure.with_density_absolutely_continuous α 𝓕 π f)) 

namespace condition_on

variables {𝓕 𝓖 : measurable_space α} (h : 𝓖 ≤ 𝓕) 
  (π : @measure α 𝓕) [@finite_measure α 𝓕 π] (f g : α → ℝ≥0∞) 
  (hf₁ : @measurable _ _ 𝓕 _ f) (hf₂ : ∫⁻[𝓕] x, f x ∂π < ∞)
  (hg₁ : @measurable _ _ 𝓕 _ g) (hg₂ : ∫⁻[𝓕] x, g x ∂π < ∞)

lemma condition_on_measurable : measurable (condition_on h π f hf₁ hf₂) :=
(exists_prop.1 (classical.some_spec 
  (@signed_measure.exists_with_density_of_absolute_continuous _ _ 
    (π.trim h) ((π .[𝓕] f).trim h) _ 
    (@measure_theory.finite_measure_trim _ _ _ _ h $ 
      @with_density.finite_measure α 𝓕 _ _ _ hf₂)
    (measure.trim_absolutely_continuous h $ 
      @measure.with_density_absolutely_continuous α 𝓕 π f)))).1

lemma condition_on_spec : 
  π.trim h . (condition_on h π f hf₁ hf₂) = (π .[𝓕] f).trim h :=
(exists_prop.1 (classical.some_spec 
  (@signed_measure.exists_with_density_of_absolute_continuous _ _ 
    (π.trim h) ((π .[𝓕] f).trim h) _ 
    (@measure_theory.finite_measure_trim _ _ _ _ h $ 
      @with_density.finite_measure α 𝓕 _ _ _ hf₂)
    (measure.trim_absolutely_continuous h $ 
      @measure.with_density_absolutely_continuous α 𝓕 π f)))).2.symm

instance : partial_order (measurable_space α) := measurable_space.partial_order

/-- Alternate formualtion of `condition_on_spec` which is more useful most of the time. 
This lemma works better with `erw` than `rw`. -/
lemma condition_on_spec' {s : set α} (hs : @measurable_set α 𝓖 s) : 
  ∫⁻ x in s, condition_on h π f hf₁ hf₂ x ∂(π.trim h) = ∫⁻[𝓕] x in s, f x ∂π :=
begin
  rw [← with_density_apply _ hs, condition_on_spec, trim_measurable_set_eq h hs, 
      with_density_apply],
  exact h _ hs
end

/-- The condition of a random variable `f` with respect to a sub-σ-algebra `𝓖` is 
*essentially unique*.

Note that in this lemma, `g` is measurable with respect to `𝓖` instead of `𝓕` 
(which is stronger than measurable w.r.t.`𝓕`). -/
lemma condition_on_essentially_unique (hg₁ : measurable g)
  (hg : ∀ ⦃s : set α⦄ (hs : @measurable_set α 𝓖 s), 
    ∫⁻ x in s, condition_on h π f hf₁ hf₂ x ∂(π.trim h) = ∫⁻[𝓕] x in s, g x ∂π) : 
  g =ᵐ[π.trim h] condition_on h π f hf₁ hf₂ :=
begin
  refine ae_eq_of_with_density_eq hg₁ (condition_on_measurable h π f hf₁ hf₂) _,
  refine measure.ext (λ s hs, _),
  rw [with_density_apply _ hs, with_density_apply _ hs, hg hs, 
      lintegral_in_trim h hg₁ hs]
end 

lemma condition_on_add : 
  condition_on h π (f + g) 
    (@measurable.add α 𝓕 _ _ _ _ _ _ hf₁ hg₁) 
    (@lintegral_add_lt_top α 𝓕 _ _ _ hf₁ hg₁ hf₂ hg₂)
  =ᵐ[π.trim h] condition_on h π f hf₁ hf₂ + condition_on h π g hg₁ hg₂ :=
begin
  refine filter.eventually_eq.symm (condition_on_essentially_unique _ _ _ _ _ _ _ _),
  { exact (condition_on_measurable h π f hf₁ hf₂).add 
      (condition_on_measurable h π g hg₁ hg₂) },
  { intros s hs,
    erw [condition_on_spec', @lintegral_add α 𝓕 _ _ _ hf₁ hg₁],
    rw [← condition_on_spec' h π f hf₁ hf₂, ← condition_on_spec' h π g hg₁ hg₂, 
        ← lintegral_add, lintegral_in_trim],
    refl,
    all_goals { try { exact hs } },
    { exact (condition_on_measurable h π f hf₁ hf₂).add 
        (condition_on_measurable h π g hg₁ hg₂) },
    { exact condition_on_measurable h π f hf₁ hf₂ },
    { exact condition_on_measurable h π g hg₁ hg₂ } }
end

example {f : α → ℝ≥0∞} (hf : @measurable _ _ 𝓖 _ f) (h : 𝓖 ≤ 𝓕) : 
  @measurable _ _ 𝓕 _ f := λ s hs, h _ (hf hs)

lemma condition_on_smul (r : ℝ≥0∞) (hr : r < ∞) : 
  condition_on h π (r • f) 
    (@measurable.const_smul α 𝓕 _ _ _ _ _ _ _ hf₁ r)
    (by { erw @lintegral_const_mul α 𝓕 _ _ _ hf₁, exact ennreal.mul_lt_top hr hf₂ })
  =ᵐ[π.trim h] r • condition_on h π f hf₁ hf₂ := 
begin
  refine filter.eventually_eq.symm (condition_on_essentially_unique _ _ _ _ _ _ _ _),
  { exact (condition_on_measurable h π f hf₁ hf₂).const_smul r },
  { intros s hs,
    erw [condition_on_spec', lintegral_const_mul, lintegral_const_mul],
    rw [← condition_on_spec' h π f hf₁ hf₂ hs, lintegral_in_trim],
    all_goals { try { exact hs } },
    { exact condition_on_measurable h π f hf₁ hf₂ },
    { exact λ s hs, h _ (condition_on_measurable h π f hf₁ hf₂ hs) },
    { exact hf₁ } }
end

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
