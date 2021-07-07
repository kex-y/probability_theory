import measure_theory.integration
import data.real.ereal

/-
This file contain the definition of absolutely continuous for measures.  
-/

noncomputable theory
open_locale classical big_operators nnreal ennreal

variables {α β : Type*}
variables [measurable_space α] [measurable_space β] 

namespace measure_theory

-- ↓ These are already in mathlib
def absolutely_continuous (ν μ : measure α) : Prop := 
  ∀ (A : set α) (hA₁ : measurable_set A) (hA₂ : μ A = 0), ν A = 0 

variables {μ : measure α}

infix ` << `:60 := absolutely_continuous
infix ` . `:max := measure.with_density

lemma lintegral_in_eq_zero {f : α → ℝ≥0∞} (hf : measurable f) 
  {A : set α} (hA : μ A = 0) : ∫⁻ a in A, f a ∂μ = 0 :=
begin
  rw lintegral_eq_zero_iff hf,
  ext, 
  rw measure.restrict_zero_set hA, 
  refl,
end  

lemma map_absolutely_continuous (f : α → ℝ≥0∞) (hf : measurable f) (μ : measure α) : 
  μ . f << μ :=
begin
  intros A hA₁ hA₂,
  rw with_density_apply _ hA₁,
  exact lintegral_in_eq_zero hf hA₂
end 

end measure_theory