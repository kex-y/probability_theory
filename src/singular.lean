import hahn

/- 
This file contains the definition of mutually singular measures,  
the Jordan decomposition theorem and the Lebesgue decomposition theorem.
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

@[simp] -- Surprised this is not in mathlib
lemma lintegral_univ_eq (f : α → ℝ≥0∞) : 
  ∫⁻ a in set.univ, f a ∂μ = ∫⁻ a, f a ∂μ :=
begin
  congr, rw measure.restrict_univ,
end

/-- Given two measures `μ` and `ν`, `measurable_le μ ν` is the set of measurable 
functions `f`, such that, for all measurable sets `A`, `∫⁻ x in A, f x ∂μ ≤ ν A`. 

This is useful for the Lebesgue decomposition theorem. -/
def measurable_le (μ ν : measure α) : set (α → ℝ≥0∞) :=
{ f | measurable f ∧ ∀ (A : set α) (hA : measurable_set A), ∫⁻ x in A, f x ∂μ ≤ ν A }

lemma zero_mem_measurable_le : (0 : α → ℝ≥0∞) ∈ measurable_le μ ν :=
⟨measurable_zero, λ A hA, by simp⟩

lemma min_mem_measurable_le (f g : α → ℝ≥0∞) 
  (hf : f ∈ measurable_le μ ν) (hg : measurable g) : 
  (λ a, min (f a) (g a)) ∈ measurable_le μ ν := 
⟨measurable.min hf.1 hg, 
  λ A hA, le_trans (lintegral_mono (λ _, min_le_left _ _)) (hf.2 A hA)⟩

lemma min_mem_measurable_le' (f g : α → ℝ≥0∞) 
  (hf : f ∈ measurable_le μ ν) (hg : g ∈ measurable_le μ ν) : 
  (λ a, min (f a) (g a)) ∈ measurable_le μ ν := 
min_mem_measurable_le f g hf hg.1

lemma max_mem_measurable_le (f g : α → ℝ≥0∞) 
  (hf : f ∈ measurable_le μ ν) (hg : g ∈ measurable_le μ ν) 
  (A : set α) (hA : measurable_set A): 
  ∫⁻ a in A, max (f a) (g a) ∂μ
    ≤ ∫⁻ a in A ∩ { a | f a ≤ g a }, g a ∂μ 
    + ∫⁻ a in A ∩ { a | g a < f a }, f a ∂μ := 
begin
  rw [← lintegral_indicator _ hA, ← lintegral_indicator f, 
      ← lintegral_indicator g, ← lintegral_add],
  { refine lintegral_mono (λ a, _),
    by_cases haA : a ∈ A, 
    { by_cases f a ≤ g a,
      { simp only,
        rw [set.indicator_of_mem haA, set.indicator_of_mem, set.indicator_of_not_mem, add_zero],
        simp only [le_refl, max_le_iff, and_true, h],
        { rintro ⟨_, hc⟩,
          exact false.elim ((not_lt.2 h) hc) },
        { exact ⟨haA, h⟩ } },
      { simp only,
        rw [set.indicator_of_mem haA, set.indicator_of_mem _ f, 
            set.indicator_of_not_mem, zero_add],
        simp only [true_and, le_refl, max_le_iff, le_of_lt (not_le.1 h)],
        { rintro ⟨_, hc⟩, 
          exact false.elim (h hc) },
        { exact ⟨haA, not_le.1 h⟩ } } },
    { simp [set.indicator_of_not_mem haA] } },
  { exact measurable.indicator hg.1 (measurable_set.inter hA (measurable_set_le hf.1 hg.1)) },
  { exact measurable.indicator hf.1 (measurable_set.inter hA (measurable_set_lt hg.1 hf.1)) },
  { exact measurable_set.inter hA (measurable_set_le hf.1 hg.1) },
  { exact measurable_set.inter hA (measurable_set_lt hg.1 hf.1) },
end

lemma max_mem_measurable_le' (f g : α → ℝ≥0∞) 
  (hf : f ∈ measurable_le μ ν) (hg : g ∈ measurable_le μ ν) : 
  (λ a, max (f a) (g a)) ∈ measurable_le μ ν := 
begin
  refine ⟨measurable.max hf.1 hg.1, λ A hA, _⟩,
  have h₁ := measurable_set.inter hA (measurable_set_le hf.1 hg.1),
  have h₂ := measurable_set.inter hA (measurable_set_lt hg.1 hf.1),
  refine le_trans (max_mem_measurable_le f g hf hg A hA) _,
  refine le_trans (add_le_add (hg.2 _ h₁) (hf.2 _ h₂)) _,
  { rw [← measure_union _ h₁ h₂],
    { refine le_of_eq _,
      congr, convert set.inter_union_compl A _,
      ext a, simpa },
    rintro x ⟨⟨-, hx₁⟩, -, hx₂⟩,
    exact (not_le.2 hx₂) hx₁ }
end

def M (μ ν : measure α) := (λ f : α → ℝ≥0∞, ∫⁻ x, f x ∂μ) '' measurable_le μ ν
    
lemma M_bdd_above : Sup (M μ ν) ≤ ν set.univ :=
begin
  refine Sup_le _,
  rintro _ ⟨f, ⟨hf₁, hf₂⟩, rfl⟩,
  simp only,
  rw ← lintegral_univ_eq,
  exact hf₂ set.univ measurable_set.univ,
end

variables [finite_measure μ] [finite_measure ν]

/-- The Lebesgue decomposition theorem: Given finite measures `μ` and `ν`, there exists 
measures `ν₁`, `ν₂` such that `ν₁` is mutually singular to `μ` and there exists some 
`f : α → ℝ≥0∞` such that `ν₂ = μ.with_density f`. -/
theorem exists_singular_with_density (μ ν : measure α) [finite_measure μ] [finite_measure ν] : 
  ∃ (ν₁ ν₂ : measure α) (hν : ν = ν₁ + ν₂), 
  ν₁ ⊥ μ ∧ ∃ f : α → ℝ≥0∞, ν₂ = μ.with_density f := 
begin
  have h := @exists_tendsto_Sup (ennreal.to_real '' M μ ν) _ _,
  { choose g hg₁ hg₂ using h,
    
    sorry },
  { exact ⟨0, 0, ⟨0, zero_mem_measurable_le, by simp⟩, rfl⟩ },
  { refine ⟨(ν set.univ).to_real, λ _ hr, _⟩,
    rcases hr with ⟨r, hr₁, rfl⟩,
    rw ennreal.to_real_le_to_real,
    { exact le_trans (le_Sup hr₁) M_bdd_above },
    { exact ne_of_lt (lt_of_le_of_lt (le_trans (le_Sup hr₁) M_bdd_above) (measure_lt_top _ _)) },
    { exact ne_of_lt (measure_lt_top _ _) },

  }
end

end signed_measure