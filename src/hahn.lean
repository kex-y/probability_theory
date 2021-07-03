import signed_measure

/- 
This file contains the definition of positive and negative sets and 
the Hahn decomposition theorem.
-/

noncomputable theory
open_locale classical big_operators nnreal ennreal

variables {α β : Type*} [measurable_space α]

namespace signed_measure

/-- A set `i` is positive with respect to a signed measure if for all 
measurable set `j`, `j ⊆ i`, `j` has non-negative measure. -/
def positive (s : signed_measure α) (i : set α) : Prop := 
∀ j ⊆ i, measurable_set j → 0 ≤ s.measure_of j

/-- A set `i` is negative with respect to a signed measure if for all 
measurable set `j`, `j ⊆ i`, `j` has non-positive measure. -/
def negative (s : signed_measure α) (i : set α) : Prop := 
∀ j ⊆ i, measurable_set j → s.measure_of j ≤ 0

variables {s : signed_measure α} {i j : set α}

lemma positive_nonneg_measure (hi₁ : measurable_set i) (hi₂ : s.positive i) : 
  0 ≤ s.measure_of i := 
hi₂ i set.subset.rfl hi₁

lemma negative_nonpos_measure (hi₁ : measurable_set i) (hi₂ : s.negative i) : 
  s.measure_of i ≤ 0 := 
hi₂ i set.subset.rfl hi₁

lemma positive_subset_positive (hi : s.positive i) (hij : j ⊆ i) : 
  s.positive j :=
begin
  intros k hk,
  exact hi _ (set.subset.trans hk hij),
end

lemma negative_subset_negative (hi : s.negative i) (hij : j ⊆ i) : 
  s.negative j :=
begin
  intros k hk,
  exact hi _ (set.subset.trans hk hij),
end

lemma positive_union_positive 
  (hi₁ : measurable_set i) (hi₂ : s.positive i)
  (hj₁ : measurable_set j) (hj₂ : s.positive j) : s.positive (i ∪ j) :=
begin
  intros a ha₁ ha₂,
  have h₁ := measurable_set.inter ha₂ hi₁,
  have h₂ := measurable_set.diff (measurable_set.inter ha₂ hj₁) h₁,
  rw [← set.union_inter_sdiff_eq ha₁, 
      measure_of_union (set.union_inter_sdiff_disjoint ha₁) h₁ h₂],
  refine add_nonneg (hi₂ _ (a.inter_subset_right i) h₁) _,
  exact hj₂ _ (set.subset.trans ((a ∩ j).diff_subset (a ∩ i)) (a.inter_subset_right j)) h₂,
end

lemma negative_union_negative
  (hi₁ : measurable_set i) (hi₂ : s.negative i)
  (hj₁ : measurable_set j) (hj₂ : s.negative j) : s.negative (i ∪ j) :=
begin
  intros a ha₁ ha₂,
  have h₁ := measurable_set.inter ha₂ hi₁,
  have h₂ := measurable_set.diff (measurable_set.inter ha₂ hj₁) h₁,
  rw [← set.union_inter_sdiff_eq ha₁, 
      measure_of_union (set.union_inter_sdiff_disjoint ha₁) h₁ h₂],
  refine add_nonpos (hi₂ _ (a.inter_subset_right i) h₁) _,
  exact hj₂ _ (set.subset.trans ((a ∩ j).diff_subset (a ∩ i)) (a.inter_subset_right j)) h₂,
end

lemma exists_pos_measure_of_not_negative (hi : ¬ s.negative i) : 
  ∃ (j : set α) (hj₁ : j ⊆ i) (hj₂ : measurable_set j), 0 < s.measure_of j :=
begin
  rw negative at hi,
  push_neg at hi,
  obtain ⟨j, hj₁, hj₂, hj⟩ := hi,
  exact ⟨j, hj₁, hj₂, hj⟩,
end

example (l : ℝ) (hl : 0 < l) : ∃ n : ℕ, (1 / (n + 1) : ℝ) < l := exists_nat_one_div_lt hl
#check nat.find

lemma exists_nat_one_div_lt_measure_of_not_negative (hi : ¬ s.negative i) :
  ∃ (n : ℕ) (j : set α) (hj₁ : j ⊆ i) (hj₂ : measurable_set j), 
  (1 / (n + 1) : ℝ) < s.measure_of j := 
let ⟨j, hj₁, hj₂, hj⟩ := exists_pos_measure_of_not_negative hi in
let ⟨n, hn⟩ := exists_nat_one_div_lt hj in ⟨n, j, hj₁, hj₂, hn⟩

-- def aux₀ :

-- def aux₀r (hi₁ : measurable_set i) (hi₂ : s.measure_of i < 0) := 
-- Sup {t | ∃ (j : set α) (hj₁ : measurable_set j) (hj₂ : j ⊆ i), t = s.measure_of j}

-- instance : has_Sup ℝ := real.has_Sup

-- noncomputable
-- def aux₀set (hi₁ : measurable_set i) (hi₂ : s.measure_of i < 0) : set α := 
-- classical.some 

-- noncomputable def aux (hi₁ : measurable_set i) (hi₂ : s.measure_of i < 0) : ℕ → ℝ × set α 
-- | 0 := sorry
-- | (n + 1) := sorry

lemma exists_positive_set (hi₁ : measurable_set i) (hi₂ : s.measure_of i < 0) : 
  ∃ (j : set α) (hj₁ : measurable_set j) (hj₂ : j ⊆ i), s.negative j ∧ s.measure_of j < 0 :=
begin
  by_cases s.negative i,
  { exact ⟨i, hi₁, set.subset.refl _, h, hi₂⟩ },
  { sorry }
end

/-- The Hahn-decomposition thoerem. -/
theorem exists_disjoint_positive_negative_union_eq :
  ∃ (i j : set α) (hi₁ : measurable_set i) (hi₂ : s.positive i) 
                  (hj₁ : measurable_set j) (hj₂ : s.negative j), 
  disjoint i j ∧ i ∪ j = set.univ :=
begin
  sorry
end

end signed_measure