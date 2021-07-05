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
  obtain ⟨i, hi₁, hi₂, hi₃⟩ := s.exists_compl_positive_negative,
  have hi₄ := measurable_set.compl hi₁,
  refine ⟨s.positive_to_measure i hi₁ hi₂, s.negative_to_measure iᶜ hi₄ hi₃, _⟩,
  refine ⟨positive_to_measure_finite hi₁ hi₂, negative_to_measure_finite hi₄ hi₃, _, _⟩,
  { refine ⟨iᶜ, hi₄, _, _⟩,
    { simp_rw [positive_to_measure_apply _ _ hi₄, 
               set.inter_compl_self, s.measure_of_empty], refl },
    { simp_rw [negative_to_measure_apply _ _ (measurable_set.compl hi₄), 
               set.inter_compl_self, s.measure_of_empty, neg_zero], refl } },
  { ext k hk,
    rw [of_sub_measure_apply hk, positive_to_measure_apply hi₁ hi₂ hk, 
        negative_to_measure_apply hi₄ hi₃ hk],
    simp only [ennreal.coe_to_real, subtype.coe_mk, ennreal.some_eq_coe, sub_neg_eq_add],
    rw [← measure_of_union _ (measurable_set.inter hi₁ hk) (measurable_set.inter hi₄ hk), 
        set.inter_comm i, set.inter_comm iᶜ, set.inter_union_compl _ _],
    rintro x ⟨⟨hx₁, _⟩, hx₂, _⟩,
    exact false.elim (hx₂ hx₁) }
end

end signed_measure