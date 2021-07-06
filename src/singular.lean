import hahn

/- 
This file contains the definition of mutually singular measures and 
the Jordan decomposition theorem.
-/

noncomputable theory
open_locale classical big_operators nnreal ennreal

variables {α β : Type*} [measurable_space α]

open measure_theory

def measure.singular (μ ν : measure α) : Prop := 
∃ (i : set α) (hi₁ : measurable_set i), μ i = 0 ∧ ν iᶜ = 0  

namespace signed_measure

infix ` ⊥ `:60 := measure.singular

variables {μ ν : measure α}

lemma singular_comm (h : μ ⊥ ν) : ν ⊥ μ :=
let ⟨i, hi, his, hit⟩ := h in 
  ⟨iᶜ, measurable_set.compl hi, hit, (compl_compl i).symm ▸ his⟩

/-- The Jordan decomposition theorem: Given a signed measure `s`, there exists 
a pair of mutually singular measures `μ` and `ν` such that `s = μ - ν`. -/
theorem exists_sigular_sub (s : signed_measure α) : 
  ∃ (μ ν : measure α) [hμ : finite_measure μ] [hν : finite_measure ν], 
    μ ⊥ ν ∧ s = @of_sub_measure _ _ μ ν hμ hν :=
begin
  obtain ⟨i, hi₁, hi₂, hi₃⟩ := s.exists_compl_positive_negative,
  have hi₄ := measurable_set.compl hi₁,
  refine ⟨s.positive_to_measure i hi₁ hi₂, s.negative_to_measure iᶜ hi₄ hi₃, _⟩,
  refine ⟨positive_to_measure_finite hi₁ hi₂, negative_to_measure_finite hi₄ hi₃, _, _⟩,
  { refine ⟨iᶜ, hi₄, _, _⟩,
    { simp_rw [positive_to_measure_apply _ _ hi₄, 
               set.inter_compl_self, s.measure_of_empty], refl },
    { simp_rw [negative_to_measure_apply _ _ (measurable_set.compl hi₄), 
               set.inter_compl_self, s.measure_of_empty, neg_zero], refl } },
  { ext k hk,
    rw [of_sub_measure_apply hk, positive_to_measure_apply hi₁ hi₂ hk, 
        negative_to_measure_apply hi₄ hi₃ hk],
    simp only [ennreal.coe_to_real, subtype.coe_mk, ennreal.some_eq_coe, sub_neg_eq_add],
    rw [← measure_of_union _ (measurable_set.inter hi₁ hk) (measurable_set.inter hi₄ hk), 
        set.inter_comm i, set.inter_comm iᶜ, set.inter_union_compl _ _],
    rintro x ⟨⟨hx₁, _⟩, hx₂, _⟩,
    exact false.elim (hx₂ hx₁) }
end

section

variables [finite_measure μ] [finite_measure ν] {r : ℝ≥0}

instance : finite_measure (μ + ν) := 
{ measure_univ_lt_top := 
  begin
    rw [measure.coe_add, pi.add_apply, ennreal.add_lt_top],
    exact ⟨measure_lt_top _ _, measure_lt_top _ _⟩,
  end }

instance : finite_measure (r • μ) := 
{ measure_univ_lt_top := 
  begin
    erw [measure.coe_smul, pi.smul_apply, algebra.id.smul_eq_mul, ennreal.coe_of_nnreal_hom],
    exact ennreal.mul_lt_top ennreal.coe_lt_top (measure_lt_top _ _),
  end }

end

lemma measure.exists_measure_pos_of_measure_Union_pos (μ : measure α) 
  (f : ℕ → set α) (hf : 0 < μ (⋃ n, f n)) : 
  ∃ n, 0 < μ (f n) :=
begin
  by_contra, push_neg at h,
  simp_rw nonpos_iff_eq_zero at h,
  refine pos_iff_ne_zero.1 hf _,
  rw ← nonpos_iff_eq_zero,
  refine le_trans (measure_Union_le (λ (i : ℕ), f i)) _,
  rw nonpos_iff_eq_zero,
  convert tsum_zero, 
  { ext1 n, exact h n },
  { apply_instance },
end

lemma exists_positive_of_sub_measure 
  (μ ν : measure α) [finite_measure μ] [finite_measure ν] (h : ¬ μ ⊥ ν) : 
  ∃ (ε : ℝ≥0) (hε : 0 < ε), ∃ (E : set α) (hE : measurable_set E) (hνE : 0 < ν E), 
  (of_sub_measure μ (ε • ν)).positive E :=
begin
  have : ∀ n : ℕ, ∃ (i : set α) (hi₁ : measurable_set i), 
    (of_sub_measure μ ((1 / (n + 1) : ℝ≥0) • ν)).positive i ∧ 
    (of_sub_measure μ ((1 / (n + 1) : ℝ≥0) • ν)).negative iᶜ,
  { intro, exact exists_compl_positive_negative _ },

  choose f hf₁ hf₂ hf₃ using this,
  set A := ⋂ n, (f n)ᶜ with hA₁,

  have hAmeas : measurable_set A,
  { exact measurable_set.Inter (λ n, measurable_set.compl (hf₁ n)) },
  have hA₂ : ∀ n : ℕ, (of_sub_measure μ ((1 / (n + 1) : ℝ≥0) • ν)).negative A,
  { intro n, exact negative_subset_negative (hf₃ n) (set.Inter_subset _ _) },
  have hA₃ : ∀ n : ℕ, μ A ≤ (1 / (n + 1) : ℝ≥0) * ν A,
  { intro n, 
    have := negative_nonpos_measure hAmeas (hA₂ n),
    rwa [of_sub_measure_apply hAmeas, sub_nonpos, ennreal.to_real_le_to_real] at this,
    exacts [ne_of_lt (measure_lt_top _ _), ne_of_lt (measure_lt_top _ _)] },
  have hμ : μ A = 0,
  { apply @ennreal.eq_zero_of_le_one_div_nat_plus_one (μ A) (ν A) _ _,
    { intro n, convert hA₃ n, simp },
    { exact ne_of_lt (measure_lt_top _ _) },
    { exact ne_of_lt (measure_lt_top _ _) } },

  rw measure.singular at h,
  push_neg at h,
  have := h _ hAmeas hμ,
  simp_rw [hA₁, set.compl_Inter, compl_compl] at this,
  obtain ⟨n, hn⟩ := measure.exists_measure_pos_of_measure_Union_pos ν _ 
    (pos_iff_ne_zero.mpr this),
  exact ⟨1 / (n + 1), by simp, f n, hf₁ n, hn, hf₂ n⟩,
end

/-- The Lebesgue decomposition theorem: Given finite measures `μ` and `ν`, there exists 
measures `ν₁`, `ν₂` such that `ν₁` is mutually singular to `μ` and there exists some 
`f : α → ℝ≥0∞` such that `ν₂ = μ.with_density f`. -/
theorem exists_singular_with_density (μ ν : measure α) [finite_measure μ] [finite_measure ν]: 
  ∃ (ν₁ ν₂ : measure α) (hν : ν = ν₁ + ν₂), 
  ν₁ ⊥ μ ∧ ∃ f : α → ℝ≥0∞, ν₂ = μ.with_density f := sorry

end signed_measure