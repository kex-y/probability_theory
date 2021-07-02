import measure_theory.integration
import data.real.ereal

/-
This file contains some lemmas that were used elsewhere but did not fit in that 
file.
-/

noncomputable theory
open_locale classical big_operators nnreal ennreal

variables {α β : Type*}
variables [measurable_space α] [measurable_space β] 

open ennreal set

section tsum

lemma tsum_to_real_of_summable {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ⊤) 
  (h : summable (ennreal.to_real ∘ f)) : 
  (∑' a, f a).to_real = ∑' a, (f a).to_real :=
begin
  obtain ⟨r, hr⟩ := h,
  rw has_sum.tsum_eq hr,
  have hr' : (ennreal.of_real r).to_real = r,
  { rw ennreal.to_real_of_real,
    rw ← has_sum.tsum_eq hr,
    apply tsum_nonneg,
    intro x,
    exact to_real_nonneg }, 
  suffices : has_sum f (ennreal.of_real r),
  { rw has_sum.tsum_eq this,
    exact hr' },
  rw has_sum at *,
  rw ← tendsto_to_real_iff,
  { convert hr, ext s,
    { rw to_real_sum,
      intros a _,
      exact lt_top_iff_ne_top.2 (hf a) } },
  { intros s hs,
    rw sum_eq_top_iff at hs,
    obtain ⟨x, _, hx⟩ := hs,
    exact (hf x) hx },
  { exact ennreal.of_real_ne_top } 
end

lemma tsum_to_real_of_not_summable {f : α → ℝ≥0∞} (hf : ∀ a, f a ≠ ⊤) 
  (h : ¬ summable (ennreal.to_real ∘ f)) : 
  (∑' a, f a).to_real = ∑' a, (f a).to_real :=
begin
  rw [tsum_eq_zero_of_not_summable h, to_real_eq_zero_iff],
  apply or.inr,
  suffices : has_sum f ⊤,
  { rw has_sum.tsum_eq this },
  rw has_sum,
  sorry
end

lemma tsum_to_real (f : α → ℝ≥0∞) (hf : ∀ a, f a ≠ ⊤) : 
  (∑' a, f a).to_real = ∑' a, (f a).to_real :=
begin
  by_cases summable (ennreal.to_real ∘ f),
  exact tsum_to_real_of_summable hf h,
  exact tsum_to_real_of_not_summable hf h,
end

end tsum

section set

lemma set.Union_eq_union {ι} (f : ι → set α) (j : ι) : 
  (⋃ i, f i) = f j ∪ ⋃ (i : ι) (hi : i ≠ j), f i :=
begin
  ext x, 
  simp only [exists_prop, mem_Union, mem_union_eq], 
  split,
  { rintro ⟨i, hi⟩,
    by_cases i = j,
    { exact or.inl (h ▸ hi) },
    { exact or.inr ⟨i, h, hi⟩ } },
  { rintro (hj | ⟨i, hij, hi⟩),
    { exact ⟨j, hj⟩ },
    { exact ⟨i, hi⟩ } }
end

end set

section real

lemma real.norm_of_neg {x : ℝ} (hx : x < 0) : ∥x∥ = -x :=
abs_of_neg hx

end real