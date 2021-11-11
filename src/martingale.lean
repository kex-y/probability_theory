import measure_theory.function.conditional_expectation

noncomputable theory
open_locale classical measure_theory nnreal ennreal topological_space

namespace measure_theory

/-- A `filtration` on measurable space `α` with σ-algebra `m` is a monotone 
sequence of of sub-σ-algebras of `m`. -/
structure filtration (α ι : Type*) [preorder ι] (m : measurable_space α) :=
(seq : ι → measurable_space α)
(mono : monotone seq) (le : ∀ i : ι, seq i ≤ m)

open topological_space

variables {α β ι : Type*} {m : measurable_space α} [measurable_space β]

/-- A measure is σ-finite with respect to filtration if it is σ-finite with respect 
to all the sub-σ-algebra of the filtration. -/
class sigma_finite_filtration [preorder ι] (μ : measure α) (f : filtration α ι m) : Prop :=
(sigma_finite : ∀ ⦃i : ι⦄, @sigma_finite α (f.seq i) (μ.trim (f.le i)))

instance sigma_finite_of_sigma_finite_filtration [preorder ι] (μ : measure α) (f : filtration α ι m)
  [hf : sigma_finite_filtration μ f] (i : ι) : 
  @sigma_finite α (f.seq i) (μ.trim (f.le i)) := 
by apply hf.sigma_finite -- can't exact here

/-- A sequence of functions `u` is adapted to a filtration `f` if for all `i`, 
`u i` is `f i`-measurable. -/
def adapted [preorder ι] (f : filtration α ι m) (u : ι → α → β) : Prop := 
∀ ⦃i : ι⦄, measurable[f.seq i] (u i)

namespace filtration

section

variable [preorder ι]

/-- Given a sequence of functions, the natural filtration is the smallest sequence 
of σ-algebras such that that sequence of functions is measurable with respect to 
the filtration. -/
def natural (u : ι → α → β) (hum : ∀ i, measurable (u i)) : filtration α ι m := 
{ seq := λ i, ⨆ j ≤ i, measurable_space.comap (u j) infer_instance,
  mono := λ i j hij, bsupr_le_bsupr' $ λ k hk, le_trans hk hij,
  le := λ i, bsupr_le (λ j hj s hs, let ⟨t, ht, ht'⟩ := hs in ht' ▸ hum j ht) }

-- move
lemma measurable_le {m m0 : measurable_space α} (hm : m ≤ m0) {f : α → β}
  (hf : measurable[m] f) : measurable[m0] f :=
λ s hs, hm _ (hf hs)

lemma adapted_natural {u : ι → α → β} (hum : ∀ i, measurable[m] (u i)) : 
  adapted (natural u hum) u := 
λ i, measurable_le (le_bsupr_of_le i (le_refl i) (le_refl _)) (λ s hs, ⟨s, hs, rfl⟩)

section is_martingale

variables {E : Type*} [normed_group E] [measurable_space E]  
  [second_countable_topology E] [normed_space ℝ E] [complete_space E] [borel_space E]

-- def is_submartingale (μ : measure α) (f : filtration α ι m) (u : ι → Lp E 1 μ) : Prop :=
-- ∀ ⦃i j : ι⦄, i ≤ j → ∀ ⦃s : set α⦄, measurable_set[f.seq i] s →
--   ∫ x in s, u i x ∂μ ≤ ∫ x in s, u j x ∂μ
  
def is_martingale (μ : measure α) (f : filtration α ι m) (u : ι → Lp E 1 μ) : Prop :=
∀ ⦃i j : ι⦄, i ≤ j → ∀ ⦃s : set α⦄, measurable_set[f.seq i] s →
  ∫ x in s, u i x ∂μ = ∫ x in s, u j x ∂μ

-- Could make `u` measurable with respect to `f` but that would be less general
lemma condexp_eq_of_is_martingale (μ : measure α) (f : filtration α ι m) 
  [sigma_finite_filtration μ f] {u : ι →  Lp E 1 μ} (hum : is_martingale μ f u) 
  (hui : ∀ i, integrable (u i) μ) {i j : ι} (hij : i ≤ j) 
  (huim : measurable[f.seq i] (u i)) : u i =ᵐ[μ] μ[u j | f.le i] := 
begin
  refine ae_eq_condexp_of_forall_set_integral_eq _ (hui j) _ _ _,
  { exact λ s hs hlt, (hui i).integrable_on },
  { exact λ s hs hlt, hum hij hs },
  { exact measurable.ae_measurable' huim } 
end

end is_martingale

end

end filtration

end measure_theory