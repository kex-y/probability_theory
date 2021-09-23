/-
The main point of this file is to prove that 
`μ.with_density f = μ.with_density g → f =ᵐ[μ] g`.

We have this already with `with_densityᵥ` due to lemmas for `integral`.
We should use these existing API to transport the lemmas to `lintegral`.
However, that might be difficult since it would require 
`∀ᵐ x ∂μ, f x < ∞` which is unnecessary mathematically.

Okay, actually the condition is necessary. Indeed, consider the 
`⊤` measure on `ℝ` which maps `∅` to `0` and `∞` otherwise. Then 
`∫ₛ 1 ∂⊤ = ∫ₛ 2 ∂⊤ = ∞` for all `s` while ¬ `1 = 2` a.e.
-/

import measure_theory.measure.with_density_vector_measure

noncomputable theory
open_locale classical measure_theory nnreal ennreal

namespace measure_theory

open topological_space

variables {α : Type*} [measurable_space α] {μ : measure α} 

lemma lintegral_sub_le (f g : α → ℝ≥0∞) 
  (hf : measurable f) (hg : measurable g) (h : f ≤ᵐ[μ] g) : 
  ∫⁻ x, g x ∂μ - ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x - f x ∂μ :=
begin
  by_cases hfi : ∫⁻ x, f x ∂μ = ∞,
  { rw [hfi, ennreal.sub_top],
    exact bot_le },
  { rw lintegral_sub hg hf hfi h,
    refl' }
end

lemma ae_le_of_ae_lt {f g : α → ℝ≥0∞} (h : ∀ᵐ x ∂μ, f x < g x) : f ≤ᵐ[μ] g :=
begin
  rw [filter.eventually_le, ae_iff],
  rw ae_iff at h,
  refine measure_mono_null (λ x hx, _) h,
  exact not_lt.2 (le_of_lt (not_le.1 hx)),
end

lemma lintegral_strict_mono {f g : α → ℝ≥0∞} (huniv : 0 < μ set.univ)
  (hf : measurable f) (hg : measurable g) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h : ∀ᵐ x ∂μ, f x < g x) : 
  ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ :=
begin 
  rw [← ennreal.sub_pos, ← lintegral_sub hg hf hfi (ae_le_of_ae_lt h)],
  by_contra hnlt, 
  rw [not_lt, nonpos_iff_eq_zero, lintegral_eq_zero_iff (hg.sub hf), filter.eventually_eq] at hnlt,
  simp only [ae_iff, ennreal.sub_eq_zero_iff_le, pi.zero_apply, not_lt, not_le] at hnlt h,
  refine huniv.ne _,
  rw [← h, ← add_zero (μ {a : α | g a ≤ f a}), ← hnlt, ← measure_union],
  { congr, ext x, 
    simp only [set.mem_univ, iff_true, set.mem_union_eq, set.mem_set_of_eq, le_or_lt] },
  { rintro x ⟨hxlt, hxgt⟩,
    exact not_lt.2 hxlt hxgt },
  { exact measurable_set_le hg hf },
  { exact measurable_set_lt hf hg }
end

lemma set_lintegral_strict_mono {f g : α → ℝ≥0∞} {s : set α} 
  (hsm : measurable_set s) (hs : 0 < μ s) (hf : measurable f) (hg : measurable g) 
  (hfi : ∫⁻ x in s, f x ∂μ ≠ ∞) (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) : 
  ∫⁻ x in s, f x ∂μ < ∫⁻ x in s, g x ∂μ :=
begin 
  refine lintegral_strict_mono _ hf hg hfi _,
  { rwa [measure.restrict_apply measurable_set.univ, set.univ_inter] },
  { rwa ae_restrict_iff' hsm }
end

lemma lt_or_gt_pos_of_ne_pos {f : α → ℝ≥0∞} (hf : measurable f) 
  {c : ℝ≥0∞} (h : 0 < μ {x | f x ≠ c}) : 
  0 < μ {x | f x < c} ∨ 0 < μ {x | f x > c} :=
begin
  by_contra hn, push_neg at hn, 
  rw [nonpos_iff_eq_zero, nonpos_iff_eq_zero] at hn,
  refine h.ne _,
  rw [← hn.2, ← zero_add (μ {x : α | f x > c}), ← hn.1, ← measure_union],
  { congr, ext x, split,
    { rintro (hlt | hgt), exacts [ne_of_lt hlt, ne_of_gt hgt] },
    { intro hn, exact ne_iff_lt_or_gt.1 hn } },
  { rintro x ⟨hxlt, hxgt⟩,
    exact not_lt.2 (le_of_lt hxlt) hxgt },
  { exact measurable_set_lt hf measurable_const },
  { exact measurable_set_lt measurable_const hf }
end

-- lemma eq_const_of_lintegral {f : α → ℝ≥0∞} (hf : measurable f) (c : ℝ≥0∞) 
--   (hfi : ∀ s : set α, ∫⁻ x in s, f x ∂μ = c * μ s) : f =ᵐ[μ] (λ _, c) :=
-- begin
--   by_cases huniv : 0 < μ set.univ,
--   { rw [filter.eventually_eq, ae_iff],
--     by_contra hμ, rw [← ne.def, ← pos_iff_ne_zero] at hμ,
--     obtain (hlt | hgt) := lt_or_gt_pos_of_ne_pos hf hμ,
--     { have := set_lintegral_strict_mono _ hlt hf measurable_const,

--     },
--     { sorry } },
--   { rw [filter.eventually_eq, ae_iff, ← nonpos_iff_eq_zero],
--     refine le_trans (measure_mono (set.subset_univ _)) (not_lt.1 huniv) }
-- end

lemma ennreal.of_real_to_real_ae_eq (f : α → ℝ≥0∞) (hf : ∀ᵐ x ∂μ, f x < ∞) : 
  (λ x, ennreal.of_real (f x).to_real) =ᵐ[μ] f :=
begin
  rw ae_iff at hf,
  rw [filter.eventually_eq, ae_iff],
  have : {x | ¬ ennreal.of_real (f x).to_real = f x} = {x | f x = ∞},
  { ext x, simp only [ne.def, set.mem_set_of_eq], split; intro hx,
    { by_contra hntop,
      exact hx (ennreal.of_real_to_real hntop) },
    { rw hx, simp } },
  rw this, 
  simpa using hf,
end 

lemma ae_eq_of_to_real_ae_eq {f g : α → ℝ≥0∞} 
  (hf : ae_measurable f μ) (hg : ae_measurable g μ) 
  (hfi : ∀ᵐ x ∂μ, f x < ∞) (hgi : ∀ᵐ x ∂μ, g x < ∞) 
  (hfg : (λ x, (f x).to_real) =ᵐ[μ] (λ x, (g x).to_real)) : 
  f =ᵐ[μ] g :=
begin
  rw [filter.eventually_eq, ae_iff] at hfg ⊢,
  simp_rw [ae_iff, not_lt, top_le_iff] at hfi hgi,
  have : {x | f x ≠ g x} ⊆ {x | (f x).to_real ≠ (g x).to_real} ∪ ({x | f x = ∞} ∪ {x | g x = ∞}),
  { intros x hx, 
    simp only [set.mem_union_eq, or_iff_not_imp_left],
    intro hx', by_contra h, push_neg at h,
    refine hx _,
    rw ← ennreal.to_real_eq_to_real h.1 h.2,
    exact not_not.1 hx' },
  refine measure_mono_null this (nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) _)),
  rw [hfg, zero_add],
  exact le_trans (measure_union_le _ _) 
    (hfi.symm ▸ hgi.symm ▸ (zero_add (0 : ℝ≥0∞)).symm ▸ le_refl _),
end

lemma ae_eq_of_forall_set_lintegral_eq {f g : α → ℝ≥0∞} 
  (hf : ae_measurable f μ) (hg : ae_measurable g μ) 
  (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (hgi : ∫⁻ x, g x ∂μ ≠ ∞)
  (hfg : ∀ ⦃s⦄, measurable_set s → μ s < ∞ → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
begin
  refine ae_eq_of_to_real_ae_eq hf hg (ae_lt_top' hf hfi) (ae_lt_top' hg hgi) 
    (integrable.ae_eq_of_forall_set_integral_eq _ _ 
      (integrable_to_real_of_lintegral_ne_top hf hfi) 
      (integrable_to_real_of_lintegral_ne_top hg hgi) (λ s hs hs', _)),
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae],
  { congr' 1,
    rw lintegral_congr_ae (ennreal.of_real_to_real_ae_eq f _),
    rw lintegral_congr_ae (ennreal.of_real_to_real_ae_eq g _),
    { exact hfg hs hs' }, 
    { refine (ae_lt_top' hg.restrict (ne_of_lt (lt_of_le_of_lt _ hgi.lt_top))),
      exact @set_lintegral_univ α _ μ g ▸ lintegral_mono_set (set.subset_univ _) },
    { refine (ae_lt_top' hf.restrict (ne_of_lt (lt_of_le_of_lt _ hfi.lt_top))),
      exact @set_lintegral_univ α _ μ f ▸ lintegral_mono_set (set.subset_univ _) } },
  { exact ae_of_all _ (λ x, ennreal.to_real_nonneg) },
  { exact ae_measurable.restrict hg.ennreal_to_real },
  { exact ae_of_all _ (λ x, ennreal.to_real_nonneg) },
  { exact ae_measurable.restrict hf.ennreal_to_real } 
end

end measure_theory