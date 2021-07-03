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

def p (s : signed_measure α) (i j : set α) (n : ℕ) : Prop := 
∃ (k : set α) (hj₁ : k ⊆ i \ j) (hj₂ : measurable_set k), (1 / (n + 1) : ℝ) < s.measure_of k

lemma exists_nat_one_div_lt_measure_of_not_negative (hi : ¬ s.negative (i \ j)) :
  ∃ (n : ℕ), s.p i j n := 
let ⟨k, hj₁, hj₂, hj⟩ := exists_pos_measure_of_not_negative hi in
let ⟨n, hn⟩ := exists_nat_one_div_lt hj in ⟨n, k, hj₁, hj₂, hn⟩

def aux₀ (s : signed_measure α) (i j : set α) : ℕ :=
if hi : ¬ s.negative (i \ j) then nat.find (exists_nat_one_div_lt_measure_of_not_negative hi) 
                       else 0
                       
lemma aux₀_spec (hi : ¬ s.negative (i \ j)) : s.p i j (s.aux₀ i j) := 
begin
  rw [aux₀, dif_pos hi],
  convert nat.find_spec _,
end

lemma aux₀_min (hi : ¬ s.negative (i \ j)) {m : ℕ} (hm : m < s.aux₀ i j) : ¬ s.p i j m := 
begin
  rw [aux₀, dif_pos hi] at hm,
  exact nat.find_min _ hm
end

def aux₁ (s : signed_measure α) (i j : set α) : set α := 
if hi : ¬ s.negative (i \ j) then classical.some (aux₀_spec hi) else ∅

lemma aux₁_spec (hi : ¬ s.negative (i \ j)) : 
  ∃ (hj₁ : (s.aux₁ i j) ⊆ i \ j) (hj₂ : measurable_set (s.aux₁ i j)), 
  (1 / (s.aux₀ i j + 1) : ℝ) < s.measure_of (s.aux₁ i j) :=
begin
  rw [aux₁, dif_pos hi],
  exact classical.some_spec (aux₀_spec hi),
end

lemma aux₁_subset : s.aux₁ i j ⊆ i \ j := 
begin
  by_cases hi : ¬ s.negative (i \ j),
  { exact let ⟨h, _⟩ := aux₁_spec hi in h },
  { rw [aux₁, dif_neg hi],
    exact set.empty_subset _ },
end

lemma aux₁_subset'' : s.aux₁ i j ⊆ i := 
set.subset.trans aux₁_subset (set.diff_subset _ _)

lemma aux₁_subset' {k : set α} (hk : i \ k ⊆ i \ j) : s.aux₁ i k ⊆ i \ j := 
begin
  by_cases hi : ¬ s.negative (i \ k),
  { exact let ⟨h, _⟩ := aux₁_spec hi in set.subset.trans h hk },
  { rw [aux₁, dif_neg hi],
    exact set.empty_subset _ },
end

lemma aux₁_measurable_set : measurable_set (s.aux₁ i j) := 
begin
  by_cases hi : ¬ s.negative (i \ j),
  { exact let ⟨_, h, _⟩ := aux₁_spec hi in h },
  { rw [aux₁, dif_neg hi],
    exact measurable_set.empty }
end

lemma aux₁_lt (hi : ¬ s.negative (i \ j)) : 
  (1 / (s.aux₀ i j + 1) : ℝ) < s.measure_of (s.aux₁ i j) :=
let ⟨_, _, h⟩ := aux₁_spec hi in h

noncomputable
def aux (s : signed_measure α) (i : set α) : ℕ → set α 
| 0 := s.aux₁ i ∅
| (n + 1) := s.aux₁ i ⋃ k ≤ n, 
  have k < n + 1 := nat.lt_succ_iff.mpr H,
  aux k

lemma aux_succ (n : ℕ) : s.aux i n.succ = s.aux₁ i ⋃ k ≤ n, s.aux i k := 
by rw aux

-- lemma aux_spec_min (n : ℕ) (h : ¬ s.negative (s.aux i n)) 
--   {m : ℕ} (hm : m < s.aux₀ (s.aux i n)) : ¬ s.p (s.aux i n) m  :=
-- aux₀_min h hm 

lemma aux_subset (n : ℕ) : 
  s.aux i n ⊆ i := 
begin
  cases n;
  { rw aux, exact aux₁_subset'' }
end

-- lemma aux_spec (n : ℕ) (h : ¬ s.negative (i \ ⋃ k ≤ n, s.aux i k)) : 
--   s.p i (s.aux i (n + 1)) (s.aux₀ i (⋃ k ≤ n, s.aux i k)) := 
-- begin
--   rw aux_succ,
--   rcases aux₀_spec h with ⟨k, hk₁, hk₂, hk₃⟩,
--   refine ⟨k, _, hk₂, hk₃⟩,
--   refine set.subset.trans hk₁ _,
--   apply set.diff_subset_diff_right,
--   -- exact aux₁_subset'' _,
--   sorry
-- end

lemma not_negative_subset (hi : ¬ s.negative i) (h : i ⊆ j) : ¬ s.negative j := 
λ h', hi $ negative_subset_negative h' h

lemma measure_of_aux 
  (hi₁ : measurable_set i) (hi₂ : ¬ s.negative i)
  (n : ℕ) (hn : ¬ s.negative (i \ ⋃ k < n, s.aux i k)) : 
  0 < s.measure_of (s.aux i n) :=
begin
  cases n,
  { rw aux, rw ← @set.diff_empty _ i at hi₂,
    rcases aux₁_spec hi₂ with ⟨_, _, h⟩,
    exact (lt_trans nat.one_div_pos_of_nat h) },
  { rw aux_succ,
    have h₁ : ¬ s.negative (i \ ⋃ (k : ℕ) (H : k ≤ n), s.aux i k),
    { apply not_negative_subset hn,
      apply set.diff_subset_diff_right,
      intros x,
      simp_rw [set.mem_Union],
      rintro ⟨n, hn₁, hn₂⟩,
      refine ⟨n, nat.lt_succ_iff.mpr hn₁, hn₂⟩ },
    rcases aux₁_spec h₁ with ⟨_, _, h⟩,
    exact (lt_trans nat.one_div_pos_of_nat h) }
end

lemma aux_measurable_set (n : ℕ) : 
  measurable_set (s.aux i n) := 
begin
  cases n,
  { rw aux,
    exact aux₁_measurable_set },
  { rw aux,
    exact aux₁_measurable_set }
end

lemma aux_lt' (hi : ¬ s.negative i) :
  (1 / (s.aux₀ i ∅ + 1) : ℝ) < s.measure_of (s.aux i 0) := 
begin 
  rw aux, 
  rw ← @set.diff_empty _ i at hi,
  exact aux₁_lt hi,
end

lemma aux_disjoint' {n m : ℕ} (h : n < m) : s.aux i n ∩ s.aux i m = ∅ :=
begin
  rw set.eq_empty_iff_forall_not_mem,
  rintro x ⟨hx₁, hx₂⟩,
  cases m, linarith,
  { rw aux at hx₂,
    exact (aux₁_subset hx₂).2 
      (set.mem_Union.2 ⟨n, set.mem_Union.2 ⟨nat.lt_succ_iff.mp h, hx₁⟩⟩) }
end

lemma aux_disjoint : pairwise (disjoint on (s.aux i)) :=
begin
  intros n m h,
  rcases lt_or_gt_of_ne h with (h | h),
  { intro x, 
    rw [set.inf_eq_inter, aux_disjoint' h],
    exact id },
  { intro x, 
    rw [set.inf_eq_inter, set.inter_comm, aux_disjoint' h],
    exact id }
end

-- lemma aux_lt'' {n : ℕ} (hn : ∀ k < n, _) 

-- lemma aux_lt (h : ∀ n : ℕ, ¬ s.negative (s.aux i n)) (n : ℕ) : 
--   (1 / (s.aux₀ (s.aux i n) + 1) : ℝ) < s.measure_of (s.aux i (n + 1)) :=
-- begin
--   cases n,
--   { rw aux, convert aux₁_lt (h 0),
    
--    },
--   { rw aux, exact aux₁_lt (h (n + 1)) }
-- end

lemma exists_positive_set (hi₁ : measurable_set i) (hi₂ : s.measure_of i < 0) : 
  ∃ (j : set α) (hj₁ : measurable_set j) (hj₂ : j ⊆ i), s.negative j ∧ s.measure_of j < 0 :=
begin
  by_cases s.negative i,
  { exact ⟨i, hi₁, set.subset.refl _, h, hi₂⟩ },
  { by_cases hn : ∀ n : ℕ, ¬ s.negative (i \ ⋃ l < n, s.aux i l),
    { sorry },
    { push_neg at hn,
      set k := nat.find hn with hk₁,
      have hk₂ : s.negative (i \ ⋃ l < k, s.aux i l) := nat.find_spec hn,
      have hmeas : measurable_set (⋃ (l : ℕ) (H : l < k), s.aux i l), 
        exact (measurable_set.Union $ λ _, 
          measurable_set.Union_Prop (λ _, aux_measurable_set _)),
      refine ⟨i \ ⋃ l < k, s.aux i l, measurable_set.diff hi₁ hmeas, 
              set.diff_subset _ _, hk₂, _⟩,
      rw measure_of_diff' hmeas hi₁,
      rw s.m_Union,
      { have h₁ : ∀ l < k, 0 ≤ s.measure_of (s.aux i l),
        { intros l hl,
          exact le_of_lt (measure_of_aux hi₁ h _ 
            (not_negative_subset (nat.find_min hn hl) (set.subset.refl _))) },
        suffices : 0 ≤ ∑' (l : ℕ), s.measure_of (⋃ (H : l < k), s.aux i l),
          linarith,
        refine tsum_nonneg _,
        intro l, by_cases l < k,
        { convert h₁ _ h,
          ext, 
          rw [set.mem_Union, exists_prop, and_iff_right_iff_imp],
          exact λ _, h },
        { convert le_of_eq s.empty.symm,
          ext, simp only [exists_prop, set.mem_empty_eq, set.mem_Union, not_and, iff_false],
          exact λ h', false.elim (h h') } },
      { intro, exact measurable_set.Union_Prop (λ _, aux_measurable_set _) },
      { intros a b hab x hx,
        simp only [exists_prop, set.mem_Union, set.mem_inter_eq, set.inf_eq_inter] at hx,
        exact let ⟨⟨_, hx₁⟩, _, hx₂⟩ := hx in aux_disjoint a b hab ⟨hx₁, hx₂⟩ },
      { apply set.Union_subset,
        intros a x, 
        simp only [and_imp, exists_prop, set.mem_Union],
        intros _ hx,
        exact aux_subset _ hx } } }
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