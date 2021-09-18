import probability_density

noncomputable theory
open_locale classical measure_theory nnreal ennreal

namespace measure_theory

open measure_theory measure_theory.measure topological_space real

variables {α β : Type*} [measurable_space α] [measurable_space β] 
variables {E : Type*} [inner_product_space ℝ E] [measurable_space E] 
  [second_countable_topology E] [complete_space E] [borel_space E] 
  
local notation `⟪`x`, `y`⟫` := @inner ℝ E _ x y

/-- The Laplace transform of a measure on some set. -/
def laplace_transform (μ : measure E) (support : set E) : E → ℝ := 
λ s, ∫ x in support, exp (-⟪s, x⟫) ∂μ

-- make it localized 
notation `𝓛 ` μ:75 := laplace_transform μ set.univ
notation `𝓛 ` μ ` on ` support:75 := laplace_transform μ support

@[measurability]
lemma measurable_inner_right (x : E) : measurable (λ y, ⟪x, y⟫) :=
(inner_right x).continuous.measurable

/-- If `S` is a region of the domain such that for all `s ∈ S`, `x ∈ support` we have 
`⟪s, x⟫ ≥0`, then the Laplace transformation exists in `S`. This is mostly useful for 
proving properties of the Laplace transform with the support being [0, ∞). -/
lemma integrable_on_exp_neg_inner {μ : measure E} {support S : set E} 
  (hsupport : μ support < ∞) (hS : ∀ ⦃s x⦄, s ∈ S → x ∈ support → 0 ≤ ⟪s, x⟫)
  {s : E} (hs : s ∈ S) : integrable_on (λ x, exp (-⟪s, x⟫)) support μ :=
begin
  refine ⟨by measurability, _⟩,
  refine lt_of_le_of_lt (set_lintegral_mono_on _ (@measurable_const _ _ _ _ 1) _) _,
  { measurability },
  { intros x hx,
    specialize hS hs hx,
    rw [ennreal.coe_le_one_iff, nnnorm_of_nonneg (le_of_lt (exp_pos _))],
    change _ ≤ (⟨1, zero_le_one⟩ : ℝ≥0),
    simp [hS] },
  { rwa [set_lintegral_const, one_mul] }
end

section

variables {μ ν : measure E} {support : set E}

lemma laplace_transform_add {s : E} 
  (hμs : integrable_on (λ x, exp (-⟪s, x⟫)) support μ)
  (hνs : integrable_on (λ x, exp (-⟪s, x⟫)) support ν) : 
  (𝓛 (μ + ν) on support) s = (𝓛 μ on support) s + (𝓛 ν on support) s :=
begin
  simp only [laplace_transform, restrict_add, pi.add_apply],
  rw [integral_add_measure hμs hνs]
end

lemma laplace_transform_smul {s : E} {c : ℝ≥0} : 
  (𝓛 (c • μ) on support) s = c • (𝓛 μ on support) s := 
begin
  simp only [laplace_transform],
  erw [restrict_smul, integral_smul_measure],
  refl
end

-- needs pr
lemma restrict_with_density 
  (μ : measure α) (f : α → ℝ≥0∞) {s : set α} (hs : measurable_set s) :
  (μ.with_density f).restrict s = (μ.restrict s).with_density f :=
begin
  ext1 t ht,
  rw [restrict_apply ht, with_density_apply _ ht, 
      with_density_apply _ (ht.inter hs), restrict_restrict ht],
end

-- needs pr
lemma set_lintegral_with_density_eq_lintegral_mul (μ : measure α) {f g : α → ℝ≥0∞}
  (hf : measurable f) (hg : measurable g) {s : set α} (hs : measurable_set s) :
  ∫⁻ x in s, g x ∂μ.with_density f = ∫⁻ x in s, (f * g) x ∂μ :=
by rw [restrict_with_density _ _ hs, lintegral_with_density_eq_lintegral_mul _ hf hg]

/-- The Laplace transform of `μ.with_density f` on the set `S` equals 
`∫ x in S, exp (-⟪s, x⟫) * f x ∂μ`. 

The latter integral is the more commonly seen definition for the Laplace transformation 
of a function. With this lemma, if `X` is a random variable and `ℙ` is a probability measure, 
`𝓛 (map X ℙ) s = ∫ exp(-sx) * pdf X ∂λ = 𝔼[exp(-s X)]` where `λ` is the Lebesgue measure. -/
lemma laplace_transform_with_density (hsupp : measurable_set support)
  {f : E → ℝ≥0∞} (hf : measurable f) (hf' : ∀ᵐ x ∂μ, x ∈ support → f x < ∞) {s : E} :
  (𝓛 (μ.with_density f) on support) s = ∫ x in support, exp (-⟪s, x⟫) * (f x).to_real ∂μ :=
begin
  simp only [laplace_transform],
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae],
  { rw [set_lintegral_with_density_eq_lintegral_mul _ hf 
        (measurable_const.inner measurable_id').neg.exp.ennreal_of_real hsupp],
    congr' 1,
    refine set_lintegral_congr_fun hsupp 
      (filter.eventually.mp hf' (ae_of_all _ (λ x hx hmem, _))),
    rw [ennreal.of_real_mul (le_of_lt (exp_pos _)), 
        ennreal.of_real_to_real (hx hmem).ne, mul_comm], 
    refl },
  all_goals { try { measurability } },
  { exact ae_of_all _ (λ x, mul_nonneg (le_of_lt (exp_pos _)) ennreal.to_real_nonneg) },
  { refine ae_of_all _ (λ x, le_of_lt (exp_pos _)) },
end

lemma laplace_transform_map (hsupp : measurable_set support) 
  {f : E → E} (hf : measurable f) {s : E} : 
  (𝓛 (map f μ) on support) s = ∫ x in f ⁻¹' support, exp (-⟪s, f x⟫) ∂μ :=
begin
  simp only [laplace_transform],
  rw set_integral_map hsupp _ hf,
  measurability,
end

/-- Given a measure `μ`, the Laplace transform of `μ.with_density (x ↦ exp(-⟪t, x⟫))` at `s` 
equals the Laplace transform of `μ` at `s + t`. -/
lemma laplace_transform_with_density_add (hsupp : measurable_set support) {s t : E} :
  (𝓛 (μ.with_density (λ x, ennreal.of_real (exp (-⟪t, x⟫)))) on support) s = 
  (𝓛 μ on support) (s + t) :=
begin
  rw laplace_transform_with_density hsupp,
  { have : ∀ x, (ennreal.of_real (exp (-⟪t, x⟫))).to_real = exp (-⟪t, x⟫),
    { intro x, rw ennreal.to_real_of_real (le_of_lt (exp_pos _)) },
    simp_rw [this, ← exp_add, ← neg_add, ← inner_add_left],
    refl },
  { measurability },
  { exact (ae_of_all _ (λ x hx, ennreal.of_real_lt_top)) },
end

lemma laplace_transform_with_density_smul 
  (hsupp : measurable_set support) {s : E} {c : ℝ} :
  (𝓛 (map (λ x, c • x) μ) on support) s = (𝓛 μ on ((λ x, c • x) ⁻¹' support)) (c • s) :=
begin
  rw laplace_transform_map hsupp (measurable_id'.const_smul' c),
  simp only [laplace_transform, inner_smul_left, inner_smul_right, is_R_or_C.conj_to_real]
end

end

end measure_theory