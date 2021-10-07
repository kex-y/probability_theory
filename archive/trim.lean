import signed_radon_nikodym

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α : Type*} {m n : measurable_space α} 
variables {M : Type*} [add_comm_monoid M] [topological_space M]

namespace measure_theory

-- namespace vector_measure

-- include m n

-- @[simps]
-- def trim (v : vector_measure α M) (hle : m ≤ n) : @vector_measure α m M _ _ :=
-- { measure_of' := λ i, if measurable_set[m] i then v i else 0,
--   empty' := by rw [if_pos measurable_set.empty, v.empty],
--   not_measurable' := λ i hi, by rw if_neg hi,
--   m_Union' := λ f hf₁ hf₂,
--   begin
--     have hf₁' : ∀ k, measurable_set[n] (f k) := λ k, hle _ (hf₁ k),
--     convert v.m_Union hf₁' hf₂,
--     { ext n, rw if_pos (hf₁ n) },
--     { rw if_pos (@measurable_set.Union _ _ m _ _ hf₁) }
--   end }

-- variables {v : vector_measure α M} (hle : m ≤ n)

-- lemma trim_eq_self : v.trim le_rfl = v := 
-- begin
--   ext1 i hi,
--   exact if_pos hi,
-- end

-- lemma zero_trim (hle : m ≤ n) : (0 : vector_measure α M).trim hle = 0 :=
-- begin
--   ext1 i hi,
--   exact if_pos hi,
-- end

-- lemma trim_measurable_set_eq {i : set α} (hle : m ≤ n) (hi : measurable_set[m] i) :
--   v.trim hle i = v i :=
-- if_pos hi

-- end vector_measure

namespace signed_measure

open vector_measure

lemma with_density_signed_measure_trim_eq_integral 
  {μ : measure α} (hle : m ≤ n) {f : α → ℝ} (hf : integrable f μ) 
  {i : set α} (hi : measurable_set[m] i) : 
  (μ.with_densityᵥ f).trim hle i = ∫ x in i, f x ∂μ :=
by rw [vector_measure.trim_measurable_set_eq hle hi, 
       with_densityᵥ_apply hf (hle _ hi)]

end signed_measure

end measure_theory