import algebra.big_operators

open_locale big_operators

variables {α : Type*}

def aux₁ : set α → set α := sorry

def aux (i : set α) : ℕ → set α 
| 0 := aux₁ i
| (n + 1) := 
aux₁ $ i \ ⋃ k ≤ n, aux k -- how to apply nat.lt_succ_iff.mpr

example (n : ℕ) : ∀ k ≤ n, k < n + 1 := 
by intro k; exact nat.lt_succ_iff.mpr