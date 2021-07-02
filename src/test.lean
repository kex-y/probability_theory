import ring_theory.dedekind_domain
import data.real.ereal

open_locale big_operators classical

variables {α : Type*}

lemma finset_sum_eq_top_of_eq_top {f : α → ereal} {a : α} (hf : f a = ⊤) 
  {s : finset α} (hs : a ∈ s) : ∑ x in s, f x = ⊤ :=
begin
  apply @finset.case_strong_induction_on _ _ 
    (λ s : finset α, a ∈ s → ∑ x in s, f x = ⊤),
  { intro h, exact false.elim (finset.not_mem_empty _ h) },
  { intros b s hb h hab,
    rw finset.sum_insert hb,
    cases finset.mem_insert.1 hab with heq hmem,
    { subst heq, 
      rw [hf, top_add] },
    { rw h s (finset.subset.refl s) hmem,
      rw add_top } },
  { exact hs }
end