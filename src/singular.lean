import hahn

/- 
This file contains the definition of mutually singular measures and 
the Jordan decomposition theorem.
-/

noncomputable theory
open_locale classical big_operators nnreal ennreal

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
  obtain ⟨i, j, hi₁, hi₂, hj₁, hj₂, hdisj, huniv⟩ := 
    s.exists_disjoint_positive_negative_union_eq,
  refine ⟨s.positive_to_measure i hi₁ hi₂, s.negative_to_measure j hj₁ hj₂, _⟩,
  refine ⟨positive_to_measure_finite hi₁ hi₂, negative_to_measure_finite hj₁ hj₂, _, _⟩,
  { refine ⟨j, hj₁, _, _⟩,
    { simp_rw [positive_to_measure_apply _ _ hj₁, 
               set.disjoint_iff_inter_eq_empty.1 hdisj, s.measure_of_empty], refl },
    { simp_rw [negative_to_measure_apply _ _ (measurable_set.compl hj₁), 
               set.inter_compl_self, s.measure_of_empty, neg_zero], refl } },
  { ext,
    sorry }
end


end signed_measure