import measure_theory.integration
import data.real.ereal
import lemmas

/-
We will in this file attempt to define signed measure and develope basic APIs 
for its use.
-/

noncomputable theory
open_locale classical big_operators nnreal ennreal

variables {α β : Type*}
variables [measurable_space α]

/-- A signed measure on a measurable space `α` is a σ-additive, real-valued function 
that maps the empty set to zero. -/
structure signed_measure (α : Type*) [measurable_space α] :=
(measure_of : set α → ℝ)
(empty : measure_of ∅ = 0)
(not_measurable ⦃i : set α⦄ : ¬ measurable_set i → measure_of i = 0)
(m_Union ⦃f : ℕ → set α⦄ :
  (∀ i, measurable_set (f i)) → pairwise (disjoint on f) → 
  measure_of (⋃ i, f i) = ∑' i, measure_of (f i))

instance : has_coe_to_fun (signed_measure α) := 
⟨λ _, set α → ℝ, signed_measure.measure_of⟩

open set measure_theory

namespace signed_measure

variables {s : signed_measure α} {f : ℕ → set α}

lemma apply (s : signed_measure α) (i : set α) : s i = s.measure_of i := rfl 

@[simp]
lemma measure_of_empty (s : signed_measure α) : s ∅ = 0 := s.empty

lemma measure_of_not_measurable_set (s : signed_measure α) 
  {i : set α} (hi : ¬ measurable_set i) : s i = 0 := s.not_measurable hi

lemma measure_of_disjoint_Union (s : signed_measure α)
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  s (⋃ i, f i) = ∑' i, s (f i) := s.m_Union hf₁ hf₂

lemma ext_iff' (s t : signed_measure α) : 
  s = t ↔ ∀ i : set α, s i = t i :=
begin
  cases s, cases t, simpa [function.funext_iff], 
end

lemma ext_iff (s t : signed_measure α) : 
  s = t ↔ ∀ i : set α, measurable_set i → s i = t i :=
begin
  split,
  { rintro rfl _ _, refl },
  { rw ext_iff',
    intros h i,
    by_cases hi : measurable_set i,
    { exact h i hi },
    { simp_rw [measure_of_not_measurable_set _ hi] } } 
end

@[ext] lemma ext {s t : signed_measure α} 
  (h : ∀ i : set α, measurable_set i → s i = t i) : s = t :=
(ext_iff s t).2 h

lemma measure_Union [encodable β] {f : β → set α}
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) :
  s (⋃ i, f i) = ∑' i, s (f i) :=
begin
  rw [← encodable.Union_decode₂, ← tsum_Union_decode₂],
  apply s.m_Union,
  { exact measurable_set.bUnion_decode₂ hf₁ },
  { exact encodable.Union_decode₂_disjoint_on hf₂ },
  { exact s.empty }
end

lemma measure_of_union {A B : set α} 
  (h : disjoint A B) (hA : measurable_set A) (hB : measurable_set B) : 
  s (A ∪ B) = s A + s B :=
begin
  rw [union_eq_Union, measure_Union, tsum_fintype, fintype.sum_bool, cond, cond],
  exacts [λ b, bool.cases_on b hB hA, pairwise_disjoint_on_bool.2 h]
end

lemma measure_of_diff {A B : set α} (hA : measurable_set A) (hB : measurable_set B) 
  (h : A ⊆ B) : s A + s (B \ A) = s B :=
by rw [← measure_of_union disjoint_diff hA (hB.diff hA), union_diff_cancel h]

lemma measure_of_diff' {A B : set α} (hA : measurable_set A) (hB : measurable_set B) 
  (h : A ⊆ B) : s (B \ A) = s B - s A :=
by rw [← measure_of_diff hA hB h, add_sub_cancel']

lemma measure_of_nonneg_disjoint_union_eq_zero {s : signed_measure α} {A B : set α}
  (h : disjoint A B) (hA₁ : measurable_set A) (hB₁ : measurable_set B)
  (hA₂ : 0 ≤ s A) (hB₂ : 0 ≤ s B) 
  (hAB : s (A ∪ B) = 0) : s A = 0 := 
begin
  rw measure_of_union h hA₁ hB₁ at hAB,
  linarith,
end

lemma measure_of_nonpos_disjoint_union_eq_zero {s : signed_measure α} {A B : set α}
  (h : disjoint A B) (hA₁ : measurable_set A) (hB₁ : measurable_set B)
  (hA₂ : s A ≤ 0) (hB₂ : s B ≤ 0) 
  (hAB : s (A ∪ B) = 0) : s A = 0 := 
begin
  rw measure_of_union h hA₁ hB₁ at hAB,
  linarith,
end

lemma measure_of_Union_nonneg (hf₁ : ∀ i, measurable_set (f i)) 
  (hf₂ : pairwise (disjoint on f)) (hf₃ : ∀ i, 0 ≤ s (f i)) :
  0 ≤ s (⋃ i, f i) := 
(s.measure_of_disjoint_Union hf₁ hf₂).symm ▸ tsum_nonneg hf₃

lemma measure_of_Union_nonpos (hf₁ : ∀ i, measurable_set (f i)) 
  (hf₂ : pairwise (disjoint on f)) (hf₃ : ∀ i, s (f i) ≤ 0) :
  s (⋃ i, f i) ≤ 0 := 
(s.measure_of_disjoint_Union hf₁ hf₂).symm ▸ tsum_nonpos hf₃

private lemma summable_measure_of_nonneg 
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) 
  (hf₃ : ∀ i, 0 ≤ s (f i)) : summable (s ∘ f) :=
begin
  have := s.measure_of_disjoint_Union hf₁ hf₂,
  by_cases s (⋃ (i : ℕ), (λ (i : ℕ), f i) i) = 0,
  { suffices : ∀ i, s (f i) = 0,
    { convert summable_zero, ext i, exact this i },
    intro i, rw ← set.union_Union_neq_eq_Union f i at h,
    have hmeas : ∀ j, measurable_set (⋃ (hi : j ≠ i), f j),
    { intro j, by_cases i = j,
      { convert measurable_set.empty, 
        rw Union_eq_empty,
        exact λ hij, false.elim (hij h.symm) },
      { convert hf₁ j,
        ext x, rw [mem_Union, exists_prop, and_iff_right_iff_imp],
        exact λ _, ne.symm h } },
    refine measure_of_nonneg_disjoint_union_eq_zero _ (hf₁ i) _ (hf₃ i) _ h,
    { intros x hx,
      simp only [exists_prop, mem_Union, mem_inter_eq, inf_eq_inter] at hx,
      exact let ⟨hfi, j, hij, hfj⟩ := hx in hf₂ j i hij ⟨hfj, hfi⟩ },
    { refine measurable_set.Union hmeas },
    { refine measure_of_Union_nonneg hmeas _ _,
      { intros l m hlm x hx,
        simp only [exists_prop, mem_Union, mem_inter_eq, inf_eq_inter] at hx,
        exact hf₂ l m hlm (let ⟨⟨_, h₁⟩, _, h₂⟩ := hx in ⟨h₁, h₂⟩) },
      { intro j, by_cases i = j,
        { apply le_of_eq,
          convert s.empty.symm,
          rw Union_eq_empty,
          exact λ hij, false.elim (hij h.symm) },
        { convert hf₃ j,
          ext, rw [mem_Union, exists_prop, and_iff_right_iff_imp],
          exact λ _, ne.symm h } } } },
  { revert h, contrapose, intro h,
    rw [not_not, this, tsum_eq_zero_of_not_summable h] },
end

private lemma summable_measure_of_nonpos  
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) 
  (hf₃ : ∀ i, s (f i) ≤ 0) : summable (s ∘ f) :=
begin
  have := s.measure_of_disjoint_Union hf₁ hf₂,
  by_cases s (⋃ (i : ℕ), (λ (i : ℕ), f i) i) = 0,
  { suffices : ∀ i, s (f i) = 0,
    { convert summable_zero, ext i, exact this i },
    intro i, rw ← set.union_Union_neq_eq_Union f i at h,
    have hmeas : ∀ j, measurable_set (⋃ (hi : j ≠ i), f j),
    { intro j, by_cases i = j,
      { convert measurable_set.empty, 
        rw Union_eq_empty,
        exact λ hij, false.elim (hij h.symm) },
      { convert hf₁ j,
        ext x, rw [mem_Union, exists_prop, and_iff_right_iff_imp],
        exact λ _, ne.symm h } },
    refine measure_of_nonpos_disjoint_union_eq_zero _ (hf₁ i) _ (hf₃ i) _ h,
    { intros x hx,
      simp only [exists_prop, mem_Union, mem_inter_eq, inf_eq_inter] at hx,
      exact let ⟨hfi, j, hij, hfj⟩ := hx in hf₂ j i hij ⟨hfj, hfi⟩ },
    { refine measurable_set.Union hmeas },
    { refine measure_of_Union_nonpos hmeas _ _,
      { intros l m hlm x hx,
        simp only [exists_prop, mem_Union, mem_inter_eq, inf_eq_inter] at hx,
        exact hf₂ l m hlm (let ⟨⟨_, h₁⟩, _, h₂⟩ := hx in ⟨h₁, h₂⟩) },
      { intro j, by_cases i = j,
        { apply le_of_eq,
          convert s.empty,
          rw Union_eq_empty,
          exact λ hij, false.elim (hij h.symm) },
        { convert hf₃ j,
          ext, rw [mem_Union, exists_prop, and_iff_right_iff_imp],
          exact λ _, ne.symm h } } } },
  { revert h, contrapose, intro h,
    rw [not_not, this, tsum_eq_zero_of_not_summable h] },
end

/-- For all `n : ℕ`, `measure_of_nonneg_seq s f n` returns `f n` if `0 ≤ s (f n)` 
and `∅` otherwise. -/
def measure_of_nonneg_seq (s : signed_measure α) (f : ℕ → set α) : ℕ → set α := 
λ i, if 0 ≤ (s ∘ f) i then f i else ∅

lemma measure_of_nonneg_seq_nonneg (i : ℕ) : 
  0 ≤ s (s.measure_of_nonneg_seq f i) := 
begin
  by_cases 0 ≤ (s ∘ f) i,
  { simp_rw [measure_of_nonneg_seq, if_pos h],
    exact h },
  { simp_rw [measure_of_nonneg_seq, if_neg h, s.measure_of_empty] }
end

lemma measure_of_nonneg_seq_of_measurable_set (hf : ∀ i, measurable_set (f i)) 
  (i : ℕ) : measurable_set $ measure_of_nonneg_seq s f i :=
begin
  by_cases 0 ≤ (s ∘ f) i,
  { simp_rw [measure_of_nonneg_seq, if_pos h],
    exact hf i },
  { simp_rw [measure_of_nonneg_seq, if_neg h],
    exact measurable_set.empty }
end

lemma measure_of_nonneg_seq_of_disjoint (hf : pairwise (disjoint on f)) : 
  pairwise $ disjoint on (s.measure_of_nonneg_seq f) :=
begin
  rintro i j hij x ⟨hx₁, hx₂⟩,
  by_cases hi : 0 ≤ (s ∘ f) i,
  { by_cases hj : 0 ≤ (s ∘ f) j,
    { simp_rw [measure_of_nonneg_seq, if_pos hi] at hx₁,
      simp_rw [measure_of_nonneg_seq, if_pos hj] at hx₂,
      exact hf i j hij ⟨hx₁, hx₂⟩ },
    { simp_rw [measure_of_nonneg_seq, if_neg hj] at hx₂,
      exact false.elim hx₂ } },
  { simp_rw [measure_of_nonneg_seq, if_neg hi] at hx₁,
    exact false.elim hx₁ }
end

/-- For all `n : ℕ`, `measure_of_nonneg_seq s f n` returns `f n` if `¬ 0 ≤ s (f n)` 
and `∅` otherwise. -/
def measure_of_nonpos_seq (s : signed_measure α) (f : ℕ → set α) : ℕ → set α := 
λ i, if ¬ 0 ≤ (s ∘ f) i then f i else ∅

lemma measure_of_nonpos_seq_nonpos (i : ℕ) : 
  s (s.measure_of_nonpos_seq f i) ≤ 0 := 
begin
  by_cases ¬ 0 ≤ (s ∘ f) i,
  { simp_rw [measure_of_nonpos_seq, if_pos h],
    exact le_of_not_ge h },
  { simp_rw [measure_of_nonpos_seq, if_neg h, s.measure_of_empty] }
end

lemma measure_of_nonpos_seq_of_measurable_set (hf : ∀ i, measurable_set (f i)) 
  (i : ℕ) : measurable_set $ measure_of_nonpos_seq s f i :=
begin
  by_cases ¬ 0 ≤ (s ∘ f) i,
  { simp_rw [measure_of_nonpos_seq, if_pos h],
    exact hf i },
  { simp_rw [measure_of_nonpos_seq, if_neg h],
    exact measurable_set.empty }
end

lemma measure_of_nonpos_seq_of_disjoint (hf : pairwise (disjoint on f)) : 
  pairwise $ disjoint on (s.measure_of_nonpos_seq f) :=
begin
  rintro i j hij x ⟨hx₁, hx₂⟩,
  by_cases hi : ¬ 0 ≤ (s ∘ f) i,
  { by_cases hj : ¬ 0 ≤ (s ∘ f) j,
    { simp_rw [measure_of_nonpos_seq, if_pos hi] at hx₁,
      simp_rw [measure_of_nonpos_seq, if_pos hj] at hx₂,
      exact hf i j hij ⟨hx₁, hx₂⟩ },
    { simp_rw [measure_of_nonpos_seq, if_neg hj] at hx₂,
      exact false.elim hx₂ } },
  { simp_rw [measure_of_nonpos_seq, if_neg hi] at hx₁,
    exact false.elim hx₁ }
end

lemma measure_of_seq_eq (i : ℕ) : 
  ∥s (f i)∥ = s (s.measure_of_nonneg_seq f i) - s (s.measure_of_nonpos_seq f i) :=
begin
  rw [measure_of_nonneg_seq, measure_of_nonpos_seq],
  by_cases 0 ≤ (s ∘ f) i,
  { have : ¬¬0 ≤ (s ∘ f) i := not_not.2 h,
    simp_rw [real.norm_of_nonneg h, if_pos h, if_neg this, 
             s.measure_of_empty, _root_.sub_zero] },
  { simp_rw [real.norm_of_neg (lt_of_not_ge h), if_pos h, if_neg h,
             s.measure_of_empty, _root_.zero_sub] }
end

/-- Given a signed measure `s`, `s ∘ f` is summable for all sequence 
`f` of pairwise disjoint measurable sets. -/
theorem summable_measure_of 
  (hf₁ : ∀ i, measurable_set (f i)) (hf₂ : pairwise (disjoint on f)) : 
  summable (s ∘ f) :=
begin
  /- 
    It suffices to show `∑ |s ∘ f| < ∞`.
    Let `N+ := { i | s(f i) ≥ 0 }`
    and `N- := { i | s(f i) < 0 }`
    Then, `Σ i, |s ∘ f i| = ∑ i ∈ N+, s ∘ f i - ∑ i ∈ N-, s ∘ f i`
    Clearly, both sum are finite since `s.range = ℝ`.  
  -/
  apply summable_of_summable_norm,
  simp_rw measure_of_seq_eq,
  apply summable.sub,
  { apply summable_measure_of_nonneg,
    { exact measure_of_nonneg_seq_of_measurable_set hf₁ },
    { exact measure_of_nonneg_seq_of_disjoint hf₂ },
    { exact measure_of_nonneg_seq_nonneg } },
  { apply summable_measure_of_nonpos,
    { exact measure_of_nonpos_seq_of_measurable_set hf₁ },
    { exact measure_of_nonpos_seq_of_disjoint hf₂ },
    { exact measure_of_nonpos_seq_nonpos } },
end

/-- A finite measure coerced into a real function is a signed measure. -/
def of_measure (μ : measure α) [hμ : finite_measure μ] : signed_measure α := 
{ measure_of := λ i : set α, if measurable_set i then (μ.measure_of i).to_real else 0,
  empty := by simp [μ.empty],
  not_measurable := λ _ hi, if_neg hi,
  m_Union := 
  begin
    intros _ hf₁ hf₂,
    rw [μ.m_Union hf₁ hf₂, ennreal.tsum_to_real_eq, if_pos (measurable_set.Union hf₁)],
    { congr, ext n, rw if_pos (hf₁ n) },
    { intros a ha,
      apply ne_of_lt hμ.measure_univ_lt_top,
      rw [eq_top_iff, ← ha, outer_measure.measure_of_eq_coe, coe_to_outer_measure],
      exact measure_mono (set.subset_univ _) }
  end }

lemma of_measure_apply_measurable {μ : measure α} [finite_measure μ] 
  {i : set α} (hi : measurable_set i) : 
  of_measure μ i = (μ i).to_real := 
if_pos hi

lemma of_measure_apply_not_measurable {μ : measure α} [finite_measure μ] 
  {i : set α} (hi : ¬ measurable_set i) : 
  of_measure μ i = 0 := 
if_neg hi

/-- The zero signed measure. -/
def zero : signed_measure α := of_measure 0

instance : has_zero (signed_measure α) := ⟨zero⟩
instance : inhabited (signed_measure α) := ⟨0⟩

@[simp]
lemma zero_apply (i : set α) : (0 : signed_measure α) i = 0 := 
begin
  by_cases measurable_set i,
  { exact of_measure_apply_measurable h },
  { exact of_measure_apply_not_measurable h }
end

/-- The negative of a signed measure is a signed measure. -/
def neg (s : signed_measure α) : signed_measure α := 
{ measure_of := -s,
  empty := by simp [s.empty],
  not_measurable := λ _ hi, by simp [s.measure_of_not_measurable_set hi],
  m_Union := 
  begin
    intros f hf₁ hf₂,
    change - _ = _,
    rw [s.measure_of_disjoint_Union hf₁ hf₂, ← tsum_neg], refl,
    exact summable_measure_of hf₁ hf₂
  end }

/-- The sum of two signed measure is a signed measure. -/
def add (s t : signed_measure α) : signed_measure α := 
{ measure_of := s + t,
  empty := by simp [s.empty, t.empty],
  not_measurable := λ _ hi,
    by simp [s.measure_of_not_measurable_set hi, t.measure_of_not_measurable_set hi],
  m_Union := 
  begin
    intros f hf₁ hf₂,
    simp only [pi.add_apply],
    rw [tsum_add, s.measure_of_disjoint_Union hf₁ hf₂, 
        t.measure_of_disjoint_Union hf₁ hf₂];
    exact summable_measure_of hf₁ hf₂
  end }

instance : has_add (signed_measure α) := ⟨add⟩
instance : has_neg (signed_measure α) := ⟨neg⟩

@[simp]
lemma neg_apply {s : signed_measure α} (i : set α) : 
  (-s) i = - s i := rfl

@[simp]
lemma add_apply {s t : signed_measure α} (i : set α) : 
  (s + t) i = s i + t i := rfl

instance : add_comm_group (signed_measure α) := 
{ add := (+), zero := (0), 
  neg := signed_measure.neg,
  add_assoc := by { intros, ext i; simp [add_assoc] },
  zero_add := by { intros, ext i; simp },
  add_zero := by { intros, ext i; simp },
  add_comm := by { intros, ext i; simp [add_comm] },
  add_left_neg := by { intros, ext i, simp } } .

/-- Given two finite measures `μ, ν`, `of_sub_measure μ ν` is the signed measure 
corresponding to the function `μ - ν`. -/
def of_sub_measure (μ ν : measure α) [hμ : finite_measure μ] [hν : finite_measure ν] : 
  signed_measure α := 
of_measure μ + - of_measure ν

lemma of_sub_measure_apply {μ ν : measure α} [finite_measure μ] [finite_measure ν] 
  {i : set α} (hi : measurable_set i) : 
  of_sub_measure μ ν i = (μ i).to_real - (ν i).to_real :=
begin
  rw [of_sub_measure, add_apply, neg_apply, of_measure_apply_measurable hi, 
      of_measure_apply_measurable hi, sub_eq_add_neg]
end

/-- Given a real number `r` and a signed measure `s`, `smul r s` is the signed 
measure corresponding to the function `r • s`. -/
def smul (r : ℝ) (s : signed_measure α) : signed_measure α := 
{ measure_of := r • s,
  empty := by simp,
  not_measurable := λ _ hi, by simp [s.measure_of_not_measurable_set hi],
  m_Union := 
  begin
    intros f hf₁ hf₂,
    rw [pi.smul_apply, s.measure_of_disjoint_Union hf₁ hf₂, ← tsum_smul], refl,
    exact summable_measure_of hf₁ hf₂
  end }

instance : has_scalar ℝ (signed_measure α) := ⟨smul⟩

@[simp]
lemma smul_apply {s : signed_measure α} {r : ℝ} (i : set α) : 
  (r • s) i = r • s i := rfl

instance : module ℝ (signed_measure α) := 
{ one_smul := by { intros, ext i; simp [one_smul] },
  mul_smul := by { intros, ext i; simp [mul_smul] },
  smul_add := by { intros, ext i; simp [smul_add] },
  smul_zero := by { intros, ext i; simp [smul_zero] },
  add_smul := by { intros, ext i; simp [add_smul] },
  zero_smul := by { intros, ext i; simp [zero_smul] } } .

end signed_measure