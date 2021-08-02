import hahn

/- 
This file contains the definition of mutually singular measures,  
the Jordan decomposition theorem and the Lebesgue decomposition theorem.
-/

noncomputable theory
open_locale classical big_operators nnreal ennreal

section PR

variables {α : Type*}

lemma measurable_set.symm_diff [measurable_space α] {u v : set α} 
  (hu : measurable_set u) (hv : measurable_set v) : measurable_set (u Δ v) := 
(hu.diff hv).union (hv.diff hu)

end PR

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

/-- A Jordan decomposition provides a Hahn decomposition. -/
lemma exists_compl_positive_negative_of_exists_sigular_sub 
  {s : signed_measure α} {μ ν : measure α}
  [hμ : finite_measure μ] [hν : finite_measure ν] 
  (h : μ ⊥ ν ∧ s = @of_sub_measure _ _ μ ν hμ hν) :
  ∃ S (hS₁ : measurable_set S) (hS₄: s.negative S) (hS₅: s.positive Sᶜ), 
  μ S = 0 ∧ ν Sᶜ = 0 :=
begin
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, h₁⟩ := h,
  refine ⟨S, hS₁, _, _, hS₂, hS₃⟩,
  { intros A hA hA₁,
    rw [h₁, of_sub_measure_apply hA₁, 
        show μ A = 0, by exact nonpos_iff_eq_zero.1 (hS₂ ▸ measure_mono hA), 
        ennreal.zero_to_real, zero_sub, neg_le, neg_zero],
    exact ennreal.to_real_nonneg },
  { intros A hA hA₁,
    rw [h₁, of_sub_measure_apply hA₁, 
        show ν A = 0, by exact nonpos_iff_eq_zero.1 (hS₃ ▸ measure_mono hA), 
        ennreal.zero_to_real, sub_zero],
    exact ennreal.to_real_nonneg },
end 

lemma subset_positive_null_set {s : signed_measure α} {u w t : set α} 
  (hw : measurable_set w) (ht : measurable_set t)
  (hsu : s.positive u) (ht₁ : s t = 0) (ht₂ : t ⊆ u) (hwt : w ⊆ t) : s w = 0 :=
begin
  have : s w + s (t \ w) = 0,
  { rw [← ht₁, ← measure_of_union set.disjoint_diff hw (ht.diff hw), 
        set.union_diff_self, set.union_eq_self_of_subset_left hwt] },
  rw add_eq_zero_iff' at this,
  exacts [this.1, hsu _ (hwt.trans ht₂) hw, hsu _ ((t.diff_subset w).trans ht₂) (ht.diff hw)],
end

lemma subset_negative_null_set {s : signed_measure α} {u w t : set α} 
  (hw : measurable_set w) (ht : measurable_set t)
  (hsu : s.negative u) (ht₁ : s t = 0) (ht₂ : t ⊆ u) (hwt : w ⊆ t) : s w = 0 :=
begin
  have : s w + s (t \ w) = 0,
  { rw [← ht₁, ← measure_of_union set.disjoint_diff hw (ht.diff hw), 
        set.union_diff_self, set.union_eq_self_of_subset_left hwt] },
  linarith [hsu _ (hwt.trans ht₂) hw, hsu _ ((t.diff_subset w).trans ht₂) (ht.diff hw)]
end

lemma set.diff_disjoint_diff (u v : set α) : disjoint (u \ v) (v \ u) :=
set.disjoint_of_subset_left (u.diff_subset v) set.disjoint_diff

lemma of_diff_eq_zero_of_symm_diff_eq_zero_positive {s : signed_measure α} {u v : set α} 
  (hu : measurable_set u) (hv : measurable_set v) 
  (hsu : s.positive u) (hsv : s.positive v) (hs : s (u Δ v) = 0) : 
  s (u \ v) = 0 ∧ s (v \ u) = 0 := 
begin
  rwa [← add_eq_zero_iff' (hsu _ (u.diff_subset v) (hu.diff hv)) 
           (hsv _ (v.diff_subset u) (hv.diff hu)), 
       ← measure_of_union (set.diff_disjoint_diff u v) (hu.diff hv) (hv.diff hu)]
end

lemma of_diff_eq_zero_of_symm_diff_eq_zero_negative {s : signed_measure α} {u v : set α} 
  (hu : measurable_set u) (hv : measurable_set v) 
  (hsu : s.negative u) (hsv : s.negative v) (hs : s (u Δ v) = 0) : 
  s (u \ v) = 0 ∧ s (v \ u) = 0 := 
begin
  have a := hsu _ (u.diff_subset v) (hu.diff hv),
  have b := hsv _ (v.diff_subset u) (hv.diff hu),
  erw [measure_of_union (set.diff_disjoint_diff u v) (hu.diff hv) (hv.diff hu)] at hs,
  split; linarith,
end

lemma of_diff_of_symm_diff_eq_zero {s : signed_measure α} {u v : set α} 
  (hu : measurable_set u) (hv : measurable_set v)
  (h : s (u Δ v) = 0) (h' : s (v \ u) = 0) : s (u \ v) + s v = s u :=
begin 
  symmetry,
  calc s u = s (u \ v ∪ u ∩ v) : by simp only [set.diff_union_inter]
       ... = s (u \ v) + s (u ∩ v) : 
  by { rw measure_of_union,
       { rw disjoint.comm,
         exact set.disjoint_of_subset_left (u.inter_subset_right v) set.disjoint_diff },
       { exact hu.diff hv },
       { exact hu.inter hv } }
       ... = s (u \ v) + s (u ∩ v ∪ v \ u) : 
  by { rw [measure_of_union, h', add_zero],
       { exact set.disjoint_of_subset_left (u.inter_subset_left v) set.disjoint_diff },
       { exact hu.inter hv },
       { exact hv.diff hu } }
       ... = s (u \ v) + s v : 
  by { rw [set.union_comm, set.inter_comm, set.diff_union_inter] } 
end

lemma of_inter_eq_of_symm_diff_eq_zero_positive {s : signed_measure α} {u v w : set α} 
  (hu : measurable_set u) (hv : measurable_set v) (hw : measurable_set w)
  (hsu : s.positive u) (hsv : s.positive v) (hs : s (u Δ v) = 0) : 
  s (w ∩ u) = s (w ∩ v) := 
begin
  have hwuv : s ((w ∩ u) Δ (w ∩ v)) = 0,
  { refine subset_positive_null_set _ _ (positive_union_positive hu hsu hv hsv) hs _ _,
    { exact (hw.inter hu).symm_diff (hw.inter hv) },
    { exact hu.symm_diff hv },
    { exact symm_diff_le_sup u v },
    { rintro x (⟨⟨hxw, hxu⟩, hx⟩ | ⟨⟨hxw, hxv⟩, hx⟩);
      rw [set.mem_inter_eq, not_and] at hx,
      { exact or.inl ⟨hxu, hx hxw⟩ },
      { exact or.inr ⟨hxv, hx hxw⟩ } } },
  obtain ⟨huv, hvu⟩ := of_diff_eq_zero_of_symm_diff_eq_zero_positive 
    (hw.inter hu) (hw.inter hv) 
    (positive_subset_positive hsu (w.inter_subset_right u)) 
    (positive_subset_positive hsv (w.inter_subset_right v)) hwuv,
  rw [← of_diff_of_symm_diff_eq_zero (hw.inter hu) (hw.inter hv) hwuv hvu, huv, zero_add]
end

lemma of_inter_eq_of_symm_diff_eq_zero_negative {s : signed_measure α} {u v w : set α} 
  (hu : measurable_set u) (hv : measurable_set v) (hw : measurable_set w)
  (hsu : s.negative u) (hsv : s.negative v) (hs : s (u Δ v) = 0) : 
  s (w ∩ u) = s (w ∩ v) := 
begin
  have hwuv : s ((w ∩ u) Δ (w ∩ v)) = 0,
  { refine subset_negative_null_set _ _ (negative_union_negative hu hsu hv hsv) hs _ _,
    { exact (hw.inter hu).symm_diff (hw.inter hv) },
    { exact hu.symm_diff hv },
    { exact symm_diff_le_sup u v },
    { rintro x (⟨⟨hxw, hxu⟩, hx⟩ | ⟨⟨hxw, hxv⟩, hx⟩);
      rw [set.mem_inter_eq, not_and] at hx,
      { exact or.inl ⟨hxu, hx hxw⟩ },
      { exact or.inr ⟨hxv, hx hxw⟩ } } },
  obtain ⟨huv, hvu⟩ := of_diff_eq_zero_of_symm_diff_eq_zero_negative 
    (hw.inter hu) (hw.inter hv) 
    (negative_subset_negative hsu (w.inter_subset_right u)) 
    (negative_subset_negative hsv (w.inter_subset_right v)) hwuv,
  rw [← of_diff_of_symm_diff_eq_zero (hw.inter hu) (hw.inter hv) hwuv hvu, huv, zero_add]
end

/-- The Jordan decomposition of a signed measure is unique. -/
theorem singular_sub_unique {s : signed_measure α} {μ₁ ν₁ μ₂ ν₂ : measure α} 
  [hμ₁ : finite_measure μ₁] [hν₁ : finite_measure ν₁] 
  [hμ₂ : finite_measure μ₂] [hν₂ : finite_measure ν₂] 
  (h₁ : μ₁ ⊥ ν₁ ∧ s = @of_sub_measure _ _ μ₁ ν₁ hμ₁ hν₁) 
  (h₂ : μ₂ ⊥ ν₂ ∧ s = @of_sub_measure _ _ μ₂ ν₂ hμ₂ hν₂) :
  μ₁ = μ₂ ∧ ν₁ = ν₂ :=
begin
  obtain ⟨S, hS₁, hS₂, hS₃, hS₄, hS₅⟩ := 
    exists_compl_positive_negative_of_exists_sigular_sub h₁,
  obtain ⟨T, hT₁, hT₂, hT₃, hT₄, hT₅⟩ := 
    exists_compl_positive_negative_of_exists_sigular_sub h₂,
  obtain ⟨hST₁, hST₂⟩ := of_symm_diff_compl_positive_negative hS₁.compl hT₁.compl 
    ⟨hS₃, (compl_compl S).symm ▸ hS₂⟩ ⟨hT₃, (compl_compl T).symm ▸ hT₂⟩,

  rw [compl_compl, compl_compl] at hST₂,
  split,
  { refine measure_theory.measure.ext (λ i hi, _), 
    have hμ₁ : (μ₁ i).to_real = s (i ∩ Sᶜ),
    { rw [h₁.2, of_sub_measure_apply (hi.inter hS₁.compl), 
          show ν₁ (i ∩ Sᶜ) = 0, by exact nonpos_iff_eq_zero.1 
            (hS₅ ▸ measure_mono (set.inter_subset_right _ _)), 
          ennreal.zero_to_real, sub_zero],
      conv_lhs { rw ← set.inter_union_compl i S },
      rw [measure_union, show μ₁ (i ∩ S) = 0, by exact nonpos_iff_eq_zero.1 
            (hS₄ ▸ measure_mono (set.inter_subset_right _ _)), zero_add], 
      { exact set.disjoint_of_subset_left (set.inter_subset_right _ _) 
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) S.disjoint_compl) },
      { exact hi.inter hS₁ },
      { exact hi.inter hS₁.compl } },
    have hμ₂ : (μ₂ i).to_real = s (i ∩ Tᶜ),
    { rw [h₂.2, of_sub_measure_apply (hi.inter hT₁.compl), 
          show ν₂ (i ∩ Tᶜ) = 0, by exact nonpos_iff_eq_zero.1 
            (hT₅ ▸ measure_mono (set.inter_subset_right _ _)), 
          ennreal.zero_to_real, sub_zero],
      conv_lhs { rw ← set.inter_union_compl i T },
      rw [measure_union, show μ₂ (i ∩ T) = 0, by exact nonpos_iff_eq_zero.1 
            (hT₄ ▸ measure_mono (set.inter_subset_right _ _)), zero_add], 
      { exact set.disjoint_of_subset_left (set.inter_subset_right _ _) 
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) T.disjoint_compl) },
      { exact hi.inter hT₁ },
      { exact hi.inter hT₁.compl } }, 
    rw [← ennreal.to_real_eq_to_real (measure_lt_top _ _) (measure_lt_top _ _), 
        hμ₁, hμ₂],
    exact of_inter_eq_of_symm_diff_eq_zero_positive hS₁.compl hT₁.compl hi hS₃ hT₃ hST₁,
    all_goals { apply_instance } },

  { refine measure_theory.measure.ext (λ i hi, _), 
    have hν₁ : (ν₁ i).to_real = - s (i ∩ S),
    { rw [h₁.2, of_sub_measure_apply (hi.inter hS₁), 
          show μ₁ (i ∩ S) = 0, by exact nonpos_iff_eq_zero.1 
            (hS₄ ▸ measure_mono (set.inter_subset_right _ _)), 
          ennreal.zero_to_real, zero_sub],
      conv_lhs { rw ← set.inter_union_compl i S },
      rw [measure_union, show ν₁ (i ∩ Sᶜ) = 0, by exact nonpos_iff_eq_zero.1 
            (hS₅ ▸ measure_mono (set.inter_subset_right _ _)), add_zero, neg_neg], 
      { exact set.disjoint_of_subset_left (set.inter_subset_right _ _) 
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) S.disjoint_compl) },
      { exact hi.inter hS₁ },
      { exact hi.inter hS₁.compl } },
    have hν₂ : (ν₂ i).to_real = - s (i ∩ T),
    { rw [h₂.2, of_sub_measure_apply (hi.inter hT₁), 
          show μ₂ (i ∩ T) = 0, by exact nonpos_iff_eq_zero.1 
            (hT₄ ▸ measure_mono (set.inter_subset_right _ _)), 
          ennreal.zero_to_real, zero_sub],
      conv_lhs { rw ← set.inter_union_compl i T },
      rw [measure_union, show ν₂ (i ∩ Tᶜ) = 0, by exact nonpos_iff_eq_zero.1 
            (hT₅ ▸ measure_mono (set.inter_subset_right _ _)), add_zero, neg_neg], 
      { exact set.disjoint_of_subset_left (set.inter_subset_right _ _) 
          (set.disjoint_of_subset_right (set.inter_subset_right _ _) T.disjoint_compl) },
      { exact hi.inter hT₁ },
      { exact hi.inter hT₁.compl } },
    rw [← ennreal.to_real_eq_to_real (measure_lt_top _ _) (measure_lt_top _ _), 
        hν₁, hν₂, neg_eq_iff_neg_eq, neg_neg],
    exact eq.symm (of_inter_eq_of_symm_diff_eq_zero_negative hS₁ hT₁ hi hS₂ hT₂ hST₂),
    all_goals { apply_instance } }
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

lemma sup_mem_measurable_le {f g : α → ℝ≥0∞} 
  (hf : f ∈ measurable_le μ ν) (hg : g ∈ measurable_le μ ν) : 
  (λ a, f a ⊔ g a) ∈ measurable_le μ ν := 
begin
  simp_rw ennreal.sup_eq_max,
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

lemma supr_succ_eq_sup {α} (f : ℕ → α → ℝ≥0∞) (m : ℕ) (a : α) :
  (⨆ (k : ℕ) (hk : k ≤ m + 1), f k a) = f m.succ a ⊔ ⨆ (k : ℕ) (hk : k ≤ m), f k a :=
begin
  ext x,
  simp only [option.mem_def, ennreal.some_eq_coe],
  split; intro h; rw ← h, symmetry,
  all_goals { 
    set c := (⨆ (k : ℕ) (hk : k ≤ m + 1), f k a) with hc, -- What is going on?
    set d := (f m.succ a ⊔ ⨆ (k : ℕ) (hk : k ≤ m), f k a) with hd,
    suffices : c ≤ d ∧ d ≤ c,
    { change c = d, -- commenting this breaks?
      exact le_antisymm this.1 this.2 },
    rw [hc, hd],
    refine ⟨_, _⟩,
    { refine bsupr_le (λ n hn, _),
      rcases nat.of_le_succ hn with (h | h),
      { exact le_sup_of_le_right (le_bsupr n h) },
      { exact h ▸ le_sup_left } },
    { refine sup_le _ _,
      { convert @le_bsupr _ _ _ (λ i, i ≤ m + 1) _ m.succ (le_refl _), refl },
      { refine bsupr_le (λ n hn, _),
        have := (le_trans hn (nat.le_succ m)), -- repacing this breaks?
        exact (le_bsupr n this) } } },
end

lemma supr_mem_measurable_le 
  (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurable_le μ ν) (n : ℕ) : 
  (λ x, ⨆ k (hk : k ≤ n), f k x) ∈ measurable_le μ ν :=
begin
  induction n with m hm,
  { refine ⟨_, _⟩,
    { simp [(hf 0).1] },
    { intros A hA, simp [(hf 0).2 A hA] } },
  { have : (λ (a : α), ⨆ (k : ℕ) (hk : k ≤ m + 1), f k a) =  
      (λ a, f m.succ a ⊔ ⨆ (k : ℕ) (hk : k ≤ m), f k a),
    { exact funext (λ _, supr_succ_eq_sup _ _ _) },
    refine ⟨measurable_supr (λ n, measurable.supr_Prop _ (hf n).1), λ A hA, _⟩,
    rw this, exact (sup_mem_measurable_le (hf m.succ) hm).2 A hA }
end

lemma supr_mem_measurable_le' 
  (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurable_le μ ν) (n : ℕ) : 
  (⨆ k (hk : k ≤ n), f k) ∈ measurable_le μ ν :=
begin
  convert supr_mem_measurable_le f hf n,
  ext, simp
end

lemma supr_monotone (f : ℕ → α → ℝ≥0∞) : 
  monotone (λ n x, ⨆ k (hk : k ≤ n), f k x) :=
begin
  intros n m hnm x,
  simp only,
  refine bsupr_le (λ k hk, _),
  have : k ≤ m, exact le_trans hk hnm, -- same problem here
  exact le_bsupr k this,
end

lemma supr_monotone' (f : ℕ → α → ℝ≥0∞) (x : α) : 
  monotone (λ n, ⨆ k (hk : k ≤ n), f k x) :=
λ n m hnm, supr_monotone f hnm x

lemma supr_le_le (f : ℕ → α → ℝ≥0∞) (n k : ℕ) (hk : k ≤ n) : 
  f k ≤ λ x, ⨆ k (hk : k ≤ n), f k x :=
λ x, le_bsupr k hk

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

local infix ` . `:max := measure.with_density

section

open filter

lemma tendsto_supr_le (f : ℕ → α → ℝ≥0∞) (x : α) :
  tendsto (λ n, ⨆ k (hk : k ≤ n), f k x) at_top (nhds  ⨆ n k (hk : k ≤ n), f k x) :=
tendsto_at_top_supr (supr_monotone' f x)

end

lemma finite_measure_of_finite_lintegral 
  {f : α → ℝ≥0∞} (hf : ∫⁻ a, f a ∂μ < ∞) : finite_measure (μ . f) := 
{ measure_univ_lt_top := by rwa [with_density_apply _ measurable_set.univ, lintegral_univ_eq] }

lemma ennreal.to_real_sub_of_le {a b : ℝ≥0∞} (h : b ≤ a) (ha : a ≠ ∞): 
  (a - b).to_real = a.to_real - b.to_real :=
begin
  lift b to ℝ≥0 using ne_top_of_le_ne_top ha h,
  lift a to ℝ≥0 using ha,
  simp only [← ennreal.coe_sub, ennreal.coe_to_real, nnreal.coe_sub (ennreal.coe_le_coe.mp h)],
end

example (a b c : ℝ) (h : b = c) : b + a = c + a :=
begin
  exact congr_fun (congr_arg has_add.add h) a,
end

lemma ennreal.lt_add_of_pos_right {a b : ℝ≥0∞} (hb : 0 < b) (ha : a ≠ ⊤): a < a + b :=
begin
  lift a to ℝ≥0 using ha,
  by_cases b = ⊤,
  { rw [h, ennreal.add_top],
    exact ennreal.coe_lt_top },
  { lift b to ℝ≥0 using h,
    rw [← ennreal.coe_add, ennreal.coe_lt_coe],
    refine lt_add_of_pos_right a (ennreal.coe_pos.mp hb) }
end

/-- The Lebesgue decomposition theorem: Given finite measures `μ` and `ν`, there exists 
measures `ν₁`, `ν₂` such that `ν₁` is mutually singular to `μ` and there exists some 
`f : α → ℝ≥0∞` such that `ν₂ = μ.with_density f`. -/
theorem exists_singular_with_density (μ ν : measure α) [finite_measure μ] [finite_measure ν] : 
  ∃ (ν₁ ν₂ : measure α) [finite_measure ν₁] [finite_measure ν₂] (hν : ν = ν₁ + ν₂), 
  ν₁ ⊥ μ ∧ ∃ (f : α → ℝ≥0∞) (hf : measurable f), ν₂ = μ . f := 
begin
  have h := @ennreal.exists_tendsto_Sup (M μ ν) _,
  { choose g hg₁ hg₂ using h,
    choose f hf₁ hf₂ using hg₁,

    set ζ := ⨆ n k (hk : k ≤ n), f k with hζ,
    have hζ₁ : Sup (M μ ν) = ∫⁻ a, ζ a ∂μ,
    { have := @lintegral_tendsto_of_tendsto_of_monotone _ _ μ 
        (λ n, ⨆ k (hk : k ≤ n), f k) (⨆ n k (hk : k ≤ n), f k) _ _ _,
      { refine tendsto_nhds_unique _ this,
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg₂ tendsto_const_nhds _ _,
        { intro n, rw ← hf₂ n,
          apply lintegral_mono,
          simp only [supr_apply, supr_le_le f n n (le_refl _)] },
        { intro n,
          exact le_Sup ⟨⨆ (k : ℕ) (hk : k ≤ n), f k, supr_mem_measurable_le' _ hf₁ _, rfl⟩ } },
      { intro n, 
        refine measurable.ae_measurable _,
        convert (supr_mem_measurable_le _ hf₁ n).1,
        ext, simp },
      { refine filter.eventually_of_forall (λ a, _),
        simp [supr_monotone' f _] },
      { refine filter.eventually_of_forall (λ a, _),
        simp [tendsto_supr_le _ _] } },
    have hζm : measurable ζ,
      { convert measurable_supr (λ n, (supr_mem_measurable_le _ hf₁ n).1),
        ext, simp [hζ] },

    set ν₁ := ν - μ . ζ with hν₁,

    have hle : μ . ζ ≤ ν,
      { intros B hB,
        rw [hζ, with_density_apply _ hB],
        simp_rw [supr_apply],
        rw lintegral_supr (λ i, (supr_mem_measurable_le _ hf₁ i).1) (supr_monotone _),
        exact supr_le (λ i, (supr_mem_measurable_le _ hf₁ i).2 B hB) },
    haveI : finite_measure (μ . ζ) := by
      { refine finite_measure_of_finite_lintegral _,
        have hle' := hle set.univ measurable_set.univ, 
        rw [with_density_apply _ measurable_set.univ, lintegral_univ_eq] at hle',
        exact lt_of_le_of_lt hle' (measure_lt_top _ _) },

    refine ⟨ν₁, μ . ζ, infer_instance, infer_instance, _, _, ζ, hζm, rfl⟩,
    { rw hν₁, ext1 A hA, 
      rw [measure.coe_add, pi.add_apply, measure.sub_apply hA hle, 
          add_comm, ennreal.add_sub_cancel_of_le (hle A hA)] },

    { by_contra,
      have hle : μ . ζ ≤ ν,
      { intros B hB,
        rw [hζ, with_density_apply _ hB],
        simp_rw [supr_apply],
        rw lintegral_supr (λ i, (supr_mem_measurable_le _ hf₁ i).1) (supr_monotone _),
        exact supr_le (λ i, (supr_mem_measurable_le _ hf₁ i).2 B hB) },
      haveI : finite_measure (μ . ζ) := by
      { refine finite_measure_of_finite_lintegral _,
        have hle' := hle set.univ measurable_set.univ, 
        rw [with_density_apply _ measurable_set.univ, lintegral_univ_eq] at hle',
        exact lt_of_le_of_lt hle' (measure_lt_top _ _) },

      obtain ⟨ε, hε₁, E, hE₁, hE₂, hE₃⟩ := exists_positive_of_sub_measure ν₁ μ h, 
      simp_rw hν₁ at hE₃,

      have hζle : ∀ A, measurable_set A → ∫⁻ a in A, ζ a ∂μ ≤ ν A,
      { intros A hA, rw hζ,
        simp_rw [supr_apply],
        rw lintegral_supr (λ n, (supr_mem_measurable_le _ hf₁ n).1) (supr_monotone _),
        exact supr_le (λ n, (supr_mem_measurable_le _ hf₁ n).2 A hA) },

      have hε₂ : ∀ A : set α, measurable_set A → 
        ∫⁻ a in A ∩ E, ε + ζ a ∂μ ≤ ν (A ∩ E),
      { intros A hA,
        have := hE₃ (A ∩ E) (set.inter_subset_right _ _) (measurable_set.inter hA hE₁),
        rwa [of_sub_measure_apply (measurable_set.inter hA hE₁), 
            measure.sub_apply (measurable_set.inter hA hE₁) hle, 
            ennreal.to_real_sub_of_le _ (ne_of_lt (measure_lt_top _ _)), sub_nonneg, 
            le_sub_iff_add_le, ← ennreal.to_real_add, ennreal.to_real_le_to_real, 
            measure.coe_nnreal_smul, pi.smul_apply, with_density_apply,
            show ε • μ (A ∩ E) = (ε : ℝ≥0∞) * μ (A ∩ E), by refl, 
            ← set_lintegral_const, ← lintegral_add measurable_const hζm] at this,
        { exact measurable_set.inter hA hE₁ },    
        { rw [ne.def, ennreal.add_eq_top, not_or_distrib],
          exact ⟨ne_of_lt (measure_lt_top _ _), ne_of_lt (measure_lt_top _ _)⟩ },
        { exact ne_of_lt (measure_lt_top _ _) },
        { exact ne_of_lt (measure_lt_top _ _) },
        { exact ne_of_lt (measure_lt_top _ _) },
        { rw with_density_apply _ (measurable_set.inter hA hE₁),
          exact hζle (A ∩ E) (measurable_set.inter hA hE₁) },
        { apply_instance } },

      have hζε : ζ + E.indicator (λ _, ε) ∈ measurable_le μ ν,
      { refine ⟨measurable.add hζm (measurable.indicator measurable_const hE₁), λ A hA, _⟩,
        have : ∫⁻ a in A, (ζ + E.indicator (λ _, ε)) a ∂μ = 
              ∫⁻ a in A ∩ E, ε + ζ a ∂μ + ∫⁻ a in A ∩ Eᶜ, ζ a ∂μ,
        { rw [lintegral_add measurable_const hζm, add_assoc, 
              ← lintegral_union (measurable_set.inter hA hE₁) 
                (measurable_set.inter hA (measurable_set.compl hE₁))
                (disjoint.mono (set.inter_subset_right _ _) (set.inter_subset_right _ _) 
                E.disjoint_compl), set.inter_union_compl],
          simp_rw [pi.add_apply],
          rw [lintegral_add hζm (measurable.indicator measurable_const hE₁), add_comm],
          refine congr_fun (congr_arg has_add.add _) _,
          rw [set_lintegral_const, lintegral_indicator _ hE₁, set_lintegral_const, 
              measure.restrict_apply hE₁, set.inter_comm] },
        conv_rhs { rw ← set.inter_union_compl A E },
        rw [this, measure_union (set.disjoint_inter_compl _ _) (measurable_set.inter hA hE₁) 
          (measurable_set.inter hA (measurable_set.compl hE₁))],
        exact add_le_add (hε₂ A hA) 
          (hζle (A ∩ Eᶜ) (measurable_set.inter hA (measurable_set.compl hE₁))) },

      have : ∫⁻ a, ζ a + E.indicator (λ _, ε) a ∂μ ≤ Sup (M μ ν),
      { exact le_Sup ⟨ζ + E.indicator (λ _, ε), hζε, rfl⟩ },

      refine not_lt.2 this _,  
      rw [hζ₁, lintegral_add hζm (measurable.indicator (measurable_const) hE₁), 
          lintegral_indicator _ hE₁, set_lintegral_const],
      refine ennreal.lt_add_of_pos_right (ennreal.mul_pos.2 ⟨ennreal.coe_pos.2 hε₁, hE₂⟩) _,
      rw [← lintegral_univ_eq, ← with_density_apply _ measurable_set.univ],
      exact ne_of_lt (measure_lt_top _ _) } },
  { exact ⟨0, 0, zero_mem_measurable_le, by simp⟩ },
end

lemma measure.eq_of_sub_measure_eq_zero (μ ν : measure α) [finite_measure μ] [finite_measure ν] 
  (h : of_sub_measure μ ν = 0) : μ = ν :=
begin
  refine measure_theory.measure.ext (λ i hi, _), 
  rw [← ennreal.to_real_eq_to_real (measure_lt_top _ _) (measure_lt_top _ _), 
      ← sub_eq_zero, ← of_sub_measure_apply hi, h, zero_apply], 
  all_goals { apply_instance }
end

-- duplicated `measure.with_density_absolutely_continuous` in `conditional` 
lemma with_density.absolutely_continuous (f : α → ℝ≥0∞) : μ . f ≪ μ :=
begin
  refine measure.absolutely_continuous.mk (λ A hA h, _),
  rw with_density_apply _ hA,
  exact (measure.restrict_eq_zero.2 h).symm ▸ lintegral_zero_measure _,
end

/-- The Lebesgue decomposition is unique. -/
theorem singular_with_density_unique 
  (ν₁ ν₂ μ₁ μ₂ : measure α) 
  [finite_measure ν₁] [finite_measure ν₂] [finite_measure μ₁] [finite_measure μ₂]
  (hν : ν = ν₁ + ν₂) (hμ : ν = μ₁ + μ₂)
  (h₁ : ν₁ ⊥ μ ∧ ∃ (f : α → ℝ≥0∞) (hf : measurable f), ν₂ = μ . f) 
  (h₂ : μ₁ ⊥ μ ∧ ∃ (f : α → ℝ≥0∞) (hf : measurable f), μ₂ = μ . f) :
  ν₁ = μ₁ ∧ ν₂ = μ₂ :=
begin
  obtain ⟨S, hS₁, hS₂, hS₃⟩ := h₁.1,
  obtain ⟨T, hT₁, hT₂, hT₃⟩ := h₂.1,
  
  have hsub : of_sub_measure ν₁ μ₁ = of_sub_measure μ₂ ν₂,
  { ext i hi,
    rw [of_sub_measure_apply hi, of_sub_measure_apply hi],
    suffices : (ν₁ i).to_real + (ν₂ i).to_real = (μ₁ i).to_real + (μ₂ i).to_real,
    { linarith },
    rw [← ennreal.to_real_add, ← ennreal.to_real_add, ennreal.to_real_eq_to_real, 
        ← measure.add_apply, ← measure.add_apply, ← hν, ← hμ],
    { exact (ennreal.add_lt_top.2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩) },
    { exact (ennreal.add_lt_top.2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩) },
    all_goals { exact ne_of_lt (measure_lt_top _ _) } },
  have heq : ∀ A (hA : measurable_set A), 
    of_sub_measure ν₁ μ₁ A = of_sub_measure ν₁ μ₁ (A ∩ (S ∩ T)ᶜ),
  { intros A hA,
    have : A = (A ∩ (S ∩ T)ᶜ) ∪ (A ∩ (S ∩ T)), 
    { rw [← set.inter_union_distrib_left, set.compl_union_self, set.inter_univ] },
    conv_lhs { rw this },
    rw measure_of_union (disjoint.comm.1 (set.disjoint_inter_compl A (S ∩ T))),
    suffices : (of_sub_measure ν₁ μ₁) (A ∩ (S ∩ T)) = 0,
    { rw [this, add_zero] },
    rw [of_sub_measure_apply, sub_eq_zero, ennreal.to_real_eq_to_real],
    refine eq.trans (nonpos_iff_eq_zero.1 (hS₂ ▸ measure_mono _)) 
      (eq.symm ((nonpos_iff_eq_zero.1 (hT₂ ▸ measure_mono _)))),
    { rw [set.inter_comm, set.inter_assoc],
      exact set.inter_subset_left _ _ },
    { rw ← set.inter_assoc, exact set.inter_subset_right _ _ },
    { exact measure_lt_top _ _ },
    { exact measure_lt_top _ _ },
    measurability },
  have hν₂ : ν₂ ≪ μ, 
  { obtain ⟨-, f, -, hf⟩ := h₁, rw hf,
    exact with_density.absolutely_continuous _ },
  have hμ₂ : μ₂ ≪ μ, 
  { obtain ⟨-, f, -, hf⟩ := h₂, rw hf,
    exact with_density.absolutely_continuous _ },
  have hμinter : μ (S ∩ T)ᶜ = 0,
    { rw set.compl_inter,
      refine nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) _),
      rw [hS₃, hT₃, add_zero], 
      exact le_refl _ },

  suffices : of_sub_measure ν₁ μ₁ = 0,
  { refine ⟨measure.eq_of_sub_measure_eq_zero _ _ this, 
            eq.symm (measure.eq_of_sub_measure_eq_zero _ _ _)⟩,
    rwa ← hsub },

  ext A hA,
  rw [heq A hA, hsub, of_sub_measure_apply, hν₂, hμ₂, ennreal.zero_to_real, 
      sub_zero, zero_apply],
  { exact nonpos_iff_eq_zero.1 (hμinter ▸ measure_mono (set.inter_subset_right _ _)) },
  { exact nonpos_iff_eq_zero.1 (hμinter ▸ measure_mono (set.inter_subset_right _ _)) },
  { measurability }
end

/-- The Radon-Nikodym theorem: Given two finite measures `μ` and `ν`, if `ν` is absolutely 
continuous with respect to `μ`, then there exists a measurable function `f` such that 
`f` is the derivative of `ν` with respect to `μ`. -/
theorem exists_with_density_of_absolute_continuous 
  (μ ν : measure α) [finite_measure μ] [finite_measure ν] (h : ν ≪ μ) : 
  ∃ (f : α → ℝ≥0∞) (hf : measurable f), ν = μ . f :=
begin
  obtain ⟨ν₁, ν₂, _, _, hν, ⟨E, hE₁, hE₂, hE₃⟩, f, hf₁, hf₂⟩ := 
    exists_singular_with_density μ ν,
  have : ν₁ = 0,
  { apply le_antisymm,
    { intros A hA,
      suffices : ν₁ set.univ = 0,
      { rw [measure.coe_zero, pi.zero_apply, ← this],
        exact measure_mono (set.subset_univ _) },
      rw [← set.union_compl_self E, measure_union (set.disjoint_compl E) hE₁ 
            (measurable_set.compl hE₁), hE₂, zero_add],
      have : (ν₁ + ν₂) Eᶜ = ν Eᶜ, { rw hν },
      rw [measure.coe_add, pi.add_apply, h hE₃] at this,
      exact (add_eq_zero_iff.1 this).1 },
    { exact measure.zero_le _} },
  rw [this, zero_add] at hν, 
  exact ⟨f, hf₁, hν.symm ▸ hf₂⟩,
end 

end signed_measure