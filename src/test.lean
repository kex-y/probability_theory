import analysis.asymptotics.specific_asymptotics
import measure_theory.decomposition.radon_nikodym
open filter

lemma l1 {k : ℝ} (hk₀ : 0 ≤ k) (hk₁ : k < 1) :
  (* k) ≤ᶠ[at_top] (λ x, x - 1) :=
begin
  rw [eventually_le, eventually_at_top],
  refine ⟨(1 - k)⁻¹, λ b hb, _⟩,
  suffices : b * k ≤ b * 1 - 1,
  { rwa mul_one at this },
  rw [← sub_nonneg, sub_sub, sub_add_eq_sub_sub_swap, ← mul_sub, sub_nonneg],
  refine (inv_pos_le_iff_one_le_mul _).mp hb,
  linarith,
end

example {k : ℝ} (hk₀ : 0 ≤ k) (hk₁ : k < 1) :
  (* k) ≤ᶠ[at_top] (λ x, ⌊x⌋) :=
eventually_le.trans (l1 hk₀ hk₁) $ 
  eventually_of_forall (λ x, (int.sub_one_lt_floor x).le)