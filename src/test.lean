import measure_theory.integral.set_integral

noncomputable theory
open_locale classical measure_theory nnreal ennreal

namespace measure_theory

open measure_theory measure_theory.measure topological_space real

variables {α β : Type*} [measurable_space α] [measurable_space β] 
variables {E : Type*} [normed_group E] [measurable_space E] [second_countable_topology E]
  [inner_product_space ℝ E] [complete_space E] [borel_space E] 
variables {ℙ : measure α} {μ : measure E}
  
local notation `⟪`x`, `y`⟫` := @inner ℝ E _ x y

/-- The Laplace transform of a measure on some set. -/
def laplace_transform (μ : measure E) (support : set E) : E → ℝ := 
λ s, ∫ x in support, exp (-⟪s, x⟫) ∂μ

end measure_theory