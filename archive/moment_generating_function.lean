import laplace

noncomputable theory
open_locale classical measure_theory nnreal ennreal

namespace measure_theory

open measure_theory measure_theory.measure topological_space real

variables {α β : Type*} [measurable_space α] [measurable_space β] 
variables {E : Type*} [inner_product_space ℝ E] [measurable_space E] 
  [second_countable_topology E] [complete_space E] [borel_space E] 

/-- The moment generating function of a random variable `X` is the bilateral 
Laplace transform on the law of `-X`. -/
def mgf {ℙ : measure α} (X : α → E) : E → ℝ := 𝓛 (map (-X) ℙ)

end measure_theory