import signed_measure

/- 
This file contains the definition of positive and negative sets and 
the Hahn decomposition theorem.
-/

noncomputable theory
open_locale classical big_operators nnreal ennreal

variables {α β : Type*} [measurable_space α]

namespace signed_measure

def positive (s : signed_measure α) (i : set α) : Prop := 
∀ j ⊆ i, measurable_set j → 0 ≤ s.measure_of j

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
  sorry
end

end signed_measure