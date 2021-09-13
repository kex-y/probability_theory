import measure_theory.integral.set_integral

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α β : Type*} {m : measurable_space α} {n : measurable_space β}

namespace measure_theory

namespace measure

include m n

open topological_space

variables {E : Type*} [normed_group E] [measurable_space E] [second_countable_topology E]
  [normed_space ℝ E] [complete_space E] [borel_space E] 
variables {μ : measure α} {f : α → β} (hf : measurable f) {g : β → E} {h : α → β}

/-- Change of variable formula. -/ -- Is this true for Bochner integrals?
lemma foo : ∫ x, g x ∂(map f μ) = ∫ y, g (h y) ∂μ :=
begin
  sorry
end

end measure

end measure_theory