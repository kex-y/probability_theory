import measure_theory.measurable_space

lemma disjoint_on_cond {α} {A B : set α} (h : disjoint A B) :
  pairwise (disjoint on λ (i : bool), cond i A B) :=
begin
  intros i j hij,
  cases i; cases j,
  { simp only [eq_self_iff_true, not_true, ne.def] at hij,
    exact false.elim hij },
  { intros x,
    simp only [and_imp, set.mem_empty_eq, set.mem_inter_eq, set.bot_eq_empty,
                cond, set.inf_eq_inter],
    exact λ hB hA, h ⟨hA, hB⟩ },
  { intros x,
    simp only [and_imp, set.mem_empty_eq, set.mem_inter_eq, set.bot_eq_empty,
                cond, set.inf_eq_inter],
    exact λ hA hB, h ⟨hA, hB⟩ },
  { simp only [eq_self_iff_true, not_true, ne.def] at hij,
    exact false.elim hij }
end