import topology.instances.ennreal

open_locale big_operators classical ennreal nnreal

lemma tsum_nonneg_coe_eq_top_of_not_summable (f : ℕ → ℝ≥0)
  (h : ¬ summable (λ (i : ℕ), (f i : ℝ))) :
  ∑' (a : ℕ), (f a : ℝ≥0∞) = ⊤ :=
begin
  sorry
end