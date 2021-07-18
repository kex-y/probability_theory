import singular

/- This file shows that a σ-finite measure can be decomposed disjointly. -/

noncomputable theory
open_locale classical big_operators nnreal ennreal

variables {α β : Type*} [measurable_space α] 

open measure_theory

def diff_le (S : ℕ → set α) : ℕ → set α
| 0       := S 0
| (n + 1) := S (n + 1) \ ⋃ k ≤ n, S k

lemma mem_zero_diff_le_iff (S : ℕ → set α) {x : α} : 
  x ∈ diff_le S 0 ↔ x ∈ S 0 := iff.rfl

lemma mem_succ_diff_le_iff (S : ℕ → set α) {x : α} {n : ℕ} : 
  x ∈ diff_le S n.succ ↔ x ∈ S n.succ ∧ ∀ k ≤ n, x ∉ S k := 
begin
  split;
  { rintro ⟨hx₁, hx₂⟩,
    exact ⟨hx₁, by simpa using hx₂⟩ },
end

lemma mem_diff_le (S : ℕ → set α) {x : α} {n : ℕ} (hx : x ∈ diff_le S n) : 
  x ∈ S n :=
begin
  cases n,
  exact (mem_zero_diff_le_iff S).1 hx,
  exact ((mem_succ_diff_le_iff S).1 hx).1,
end

lemma diff_le_pairwsie_disjoint (S : ℕ → set α) : 
  pairwise (disjoint on diff_le S) :=
begin
  rintro i j hij x ⟨hx₁, hx₂⟩,
  cases i; cases j,
  { exact hij rfl },
  { rw mem_succ_diff_le_iff at hx₂,
    exact hx₂.2 0 (zero_le _) hx₁ },
  { rw mem_succ_diff_le_iff at hx₁,
    exact hx₁.2 0 (zero_le _) hx₂ },
  { wlog h : i ≤ j,
    rw mem_succ_diff_le_iff at hx₂,
    by_cases h' : i.succ ≤ j,
    { exact hx₂.2 _ h' (mem_diff_le S hx₁) },
    { rw [not_le, nat.lt_succ_iff] at h',
      rw antisymm h h' at hij,
      exact hij rfl } }
end

lemma Union_diff_le_eq (S : ℕ → set α) : (⋃ n, diff_le S n) = ⋃ n, S n :=
begin
  ext x,
  rw [set.mem_Union, set.mem_Union],
  split,
  { rintro ⟨i, hx⟩,
    exact ⟨i, mem_diff_le S hx⟩ },
  { intro hx,
    by_cases hn : nat.find hx = 0,
    { exact ⟨0, (mem_zero_diff_le_iff S).2 (hn ▸ nat.find_spec hx)⟩ },
    { obtain ⟨n, hn⟩ := nat.exists_eq_succ_of_ne_zero hn,
      refine ⟨n.succ, (mem_succ_diff_le_iff S).2 ⟨hn ▸ nat.find_spec hx, 
        λ k hk, nat.find_min hx _⟩⟩, -- stupid triangle won't work in refine
      exact hn.symm ▸ nat.lt_succ_iff.mpr hk } }
end

lemma diff_le_subset (S : ℕ → set α) (n : ℕ) : diff_le S n ⊆ S n :=  
begin
  cases n,
  { exact set.subset.refl _ },
  { intros x hx,
    exact hx.1 }
end

lemma exists_disjoint_finite_spanning_sets_in (μ : measure α) [sigma_finite μ] : 
  ∃ S : μ.finite_spanning_sets_in {s | measurable_set s}, 
    pairwise (disjoint on S.set) := 
begin
  set T := μ.to_finite_spanning_sets_in with hT,
  refine ⟨⟨diff_le T.set, _, _, T.spanning ▸ Union_diff_le_eq _⟩, 
           diff_le_pairwsie_disjoint _⟩,
  { intros n, cases n, 
    { exact T.set_mem 0 },
    { exact measurable_set.diff (T.set_mem _) (measurable_set.Union 
        (λ _, measurable_set.Union_Prop (λ _, T.set_mem _))) } },
  { intro n,
    exact lt_of_le_of_lt (measure_mono (diff_le_subset T.set n)) (T.finite _) }
end