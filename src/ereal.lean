import topology.instances.ereal
import topology.instances.ennreal

noncomputable theory
open_locale classical big_operators ennreal

namespace ereal

variables {α β : Type*}

def of_real_hom : ℝ →+ ereal := 
{ to_fun := coe,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

@[simp] lemma coe_of_real_hom : ⇑of_real_hom = coe := rfl

@[simp, norm_cast] lemma coe_finset_sum {s : finset α} {f : α → ℝ} :
  ↑(∑ a in s, f a) = (∑ a in s, f a : ereal) :=
of_real_hom.map_sum f s

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

lemma ereal.eq_neg_iff {a b : ereal} (ha : a ≠ ⊤) (h : a + b = 0) : a = -b :=
begin
  revert h,
  rcases b.cases with rfl | ⟨b, rfl⟩ | rfl,
  { rw neg_bot, 
    rcases a.cases with rfl | ⟨a, rfl⟩ | rfl; norm_num },
  { rcases a.cases with rfl | ⟨a, rfl⟩ | rfl,
    { norm_num },
    { rw [← coe_add, ← coe_zero, ereal.coe_eq_coe_iff, 
          add_eq_zero_iff_eq_neg],
      rintro rfl,
      exact coe_neg _ },
    { norm_num } },
  { norm_num }
end

section tsum

variables {f g : α → ereal} {r : ℝ}

@[norm_cast] lemma has_sum_coe {f : α → ℝ} {r : ℝ} :
  has_sum (λ a, (f a : ereal)) r ↔ has_sum f r :=
begin
  have : (λ s : finset α, ∑ a in s, ↑(f a)) = (coe : ℝ → ereal) ∘ (λ s : finset α, ∑ a in s, f a),
    ext, simp,
  rw [has_sum, has_sum, this, tendsto_coe]
end

lemma tsum_coe_eq {f : α → ℝ} (h : has_sum f r) : ∑'a, (f a : ereal) = r :=
(has_sum_coe.2 h).tsum_eq

lemma coe_tsum {f : α → ℝ} (hf : summable f) : 
  ↑(∑' a, f a) = ∑' a, (f a : ereal) :=
begin
  obtain ⟨_, hr⟩ := hf,
  rw [hr.tsum_eq, ereal.tsum_coe_eq hr]
end

lemma has_sum_top_of_eq_top (hf : ∃ a, f a = ⊤) : 
  has_sum f ⊤ := 
begin
  obtain ⟨a, ha⟩ := hf,
  apply tendsto_at_top_of_eventually_const,
  swap, exact ({a} : finset α),
  intros s hs,
  change _ ⊆ _ at hs,
  rw finset.singleton_subset_iff at hs,
  exact finset_sum_eq_top_of_eq_top ha hs,
end

lemma tsum_eq_top_of_eq_top (hf : ∃ a, f a = ⊤) : ∑' a, f a = ⊤ :=
(has_sum_top_of_eq_top hf).tsum_eq

@[simp] protected lemma tsum_top [nonempty α] : ∑' a : α, (⊤ : ereal) = ⊤ :=
let ⟨a⟩ := ‹nonempty α› in tsum_eq_top_of_eq_top ⟨a, rfl⟩

lemma tsum_of_neq_top_or_bot (hf : ∀ a, f a ≠ ⊤ ∧ f a ≠ ⊥) : 
  (∑' a, (f a).to_real : ereal) = ∑' a, f a := 
tsum_congr $ λ b, (coe_to_real (hf b).1 (hf b).2)

lemma summable_to_real (hf : summable f) 
  (hf' : ∀ a, f a ≠ ⊤ ∧ f a ≠ ⊥) : 
  summable (to_real ∘ f) := 
begin
  sorry
end

lemma tsum_add (hf : summable f) (hg : summable g) 
  (h₁ : ∀ a, f a ≠ ⊤ ∧ f a ≠ ⊥) (h₂ : ∀ a, g a ≠ ⊤ ∧ g a ≠ ⊥) : 
  ∑' a, (f a + g a) = (∑' a, f a) + (∑' a, g a) :=
begin
  rw [(tsum_of_neq_top_or_bot h₁).symm, (tsum_of_neq_top_or_bot h₂).symm, 
      ← coe_tsum, ← coe_tsum, ← coe_add, ← tsum_add, coe_tsum],
  apply tsum_congr, 
  intro, simp [coe_to_real (h₁ b).1 (h₁ b).2, coe_to_real (h₂ b).1 (h₂ b).2],
  exact summable.add (summable_to_real hf h₁) (summable_to_real hg h₂),
  all_goals { exact summable_to_real hf h₁ <|> exact summable_to_real hg h₂ },
end

#exit


protected lemma tsum_le_tsum (h : ∀a, f a ≤ g a) : ∑'a, f a ≤ ∑'a, g a :=
tsum_le_tsum h ennreal.summable ennreal.summable

protected lemma sum_le_tsum {f : α → ℝ≥0∞} (s : finset α) : ∑ x in s, f x ≤ ∑' x, f x :=
sum_le_tsum s (λ x hx, zero_le _) ennreal.summable

protected lemma tsum_eq_supr_nat' {f : ℕ → ℝ≥0∞} {N : ℕ → ℕ} (hN : tendsto N at_top at_top) :
  ∑'i:ℕ, f i = (⨆i:ℕ, ∑ a in finset.range (N i), f a) :=
ennreal.tsum_eq_supr_sum' _ $ λ t,
  let ⟨n, hn⟩    := t.exists_nat_subset_range,
      ⟨k, _, hk⟩ := exists_le_of_tendsto_at_top hN 0 n in
  ⟨k, finset.subset.trans hn (finset.range_mono hk)⟩

protected lemma tsum_eq_supr_nat {f : ℕ → ℝ≥0∞} :
  ∑'i:ℕ, f i = (⨆i:ℕ, ∑ a in finset.range i, f a) :=
ennreal.tsum_eq_supr_sum' _ finset.exists_nat_subset_range

protected lemma tsum_eq_liminf_sum_nat {f : ℕ → ℝ≥0∞} :
  ∑' i, f i = filter.at_top.liminf (λ n, ∑ i in finset.range n, f i) :=
begin
  rw [ennreal.tsum_eq_supr_nat, filter.liminf_eq_supr_infi_of_nat],
  congr,
  refine funext (λ n, le_antisymm _ _),
  { refine le_binfi (λ i hi, finset.sum_le_sum_of_subset_of_nonneg _ (λ _ _ _, zero_le _)),
    simpa only [finset.range_subset, add_le_add_iff_right] using hi, },
  { refine le_trans (infi_le _ n) _,
    simp [le_refl n, le_refl ((finset.range n).sum f)], },
end

protected lemma le_tsum (a : α) : f a ≤ ∑'a, f a :=
le_tsum' ennreal.summable a


protected lemma ne_top_of_tsum_ne_top (h : ∑' a, f a ≠ ∞) (a : α) : f a ≠ ∞ :=
λ ha, h $ ennreal.tsum_eq_top_of_eq_top ⟨a, ha⟩

protected lemma tsum_mul_left : ∑'i, a * f i = a * ∑'i, f i :=
if h : ∀i, f i = 0 then by simp [h] else
let ⟨i, (hi : f i ≠ 0)⟩ := not_forall.mp h in
have sum_ne_0 : ∑'i, f i ≠ 0, from ne_of_gt $
  calc 0 < f i : lt_of_le_of_ne (zero_le _) hi.symm
    ... ≤ ∑'i, f i : ennreal.le_tsum _,
have tendsto (λs:finset α, ∑ j in s, a * f j) at_top (𝓝 (a * ∑'i, f i)),
  by rw [← show (*) a ∘ (λs:finset α, ∑ j in s, f j) = λs, ∑ j in s, a * f j,
         from funext $ λ s, finset.mul_sum];
  exact ennreal.tendsto.const_mul ennreal.summable.has_sum (or.inl sum_ne_0),
has_sum.tsum_eq this

protected lemma tsum_mul_right : (∑'i, f i * a) = (∑'i, f i) * a :=
by simp [mul_comm, ennreal.tsum_mul_left]

@[simp] lemma tsum_supr_eq {α : Type*} (a : α) {f : α → ℝ≥0∞} :
  ∑'b:α, (⨆ (h : a = b), f b) = f a :=
le_antisymm
  (by rw [ennreal.tsum_eq_supr_sum]; exact supr_le (assume s,
    calc (∑ b in s, ⨆ (h : a = b), f b) ≤ ∑ b in {a}, ⨆ (h : a = b), f b :
        finset.sum_le_sum_of_ne_zero $ assume b _ hb,
          suffices a = b, by simpa using this.symm,
          classical.by_contradiction $ assume h,
            by simpa [h] using hb
      ... = f a : by simp))
  (calc f a ≤ (⨆ (h : a = a), f a) : le_supr (λh:a=a, f a) rfl
    ... ≤ (∑'b:α, ⨆ (h : a = b), f b) : ennreal.le_tsum _)

lemma has_sum_iff_tendsto_nat {f : ℕ → ℝ≥0∞} (r : ℝ≥0∞) :
  has_sum f r ↔ tendsto (λn:ℕ, ∑ i in finset.range n, f i) at_top (𝓝 r) :=
begin
  refine ⟨has_sum.tendsto_sum_nat, assume h, _⟩,
  rw [← supr_eq_of_tendsto _ h, ← ennreal.tsum_eq_supr_nat],
  { exact ennreal.summable.has_sum },
  { exact assume s t hst, finset.sum_le_sum_of_subset (finset.range_subset.2 hst) }
end

lemma tendsto_nat_tsum (f : ℕ → ℝ≥0∞) :
  tendsto (λn:ℕ, ∑ i in finset.range n, f i) at_top (𝓝 (∑' n, f n)) :=
by { rw ← has_sum_iff_tendsto_nat, exact ennreal.summable.has_sum }

lemma to_nnreal_apply_of_tsum_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' i, f i ≠ ∞) (x : α) :
  (((ennreal.to_nnreal ∘ f) x : ℝ≥0) : ℝ≥0∞) = f x :=
coe_to_nnreal $ ennreal.ne_top_of_tsum_ne_top hf _

lemma summable_to_nnreal_of_tsum_ne_top {α : Type*} {f : α → ℝ≥0∞} (hf : ∑' i, f i ≠ ∞) :
  summable (ennreal.to_nnreal ∘ f) :=
by simpa only [←tsum_coe_ne_top_iff_summable, to_nnreal_apply_of_tsum_ne_top hf] using hf

lemma tendsto_cofinite_zero_of_tsum_lt_top {α} {f : α → ℝ≥0∞} (hf : ∑' x, f x < ∞) :
  tendsto f cofinite (𝓝 0) :=
begin
  have f_ne_top : ∀ n, f n ≠ ∞, from ennreal.ne_top_of_tsum_ne_top hf.ne,
  have h_f_coe : f = λ n, ((f n).to_nnreal : ennreal),
    from funext (λ n, (coe_to_nnreal (f_ne_top n)).symm),
  rw [h_f_coe, ←@coe_zero, tendsto_coe],
  exact nnreal.tendsto_cofinite_zero_of_summable (summable_to_nnreal_of_tsum_ne_top hf.ne),
end

lemma tendsto_at_top_zero_of_tsum_lt_top {f : ℕ → ℝ≥0∞} (hf : ∑' x, f x < ∞) :
  tendsto f at_top (𝓝 0) :=
by { rw ←nat.cofinite_eq_at_top, exact tendsto_cofinite_zero_of_tsum_lt_top hf }

protected lemma tsum_apply {ι α : Type*} {f : ι → α → ℝ≥0∞} {x : α} :
  (∑' i, f i) x = ∑' i, f i x :=
tsum_apply $ pi.summable.mpr $ λ _, ennreal.summable

lemma tsum_sub {f : ℕ → ℝ≥0∞} {g : ℕ → ℝ≥0∞} (h₁ : ∑' i, g i < ∞) (h₂ : g ≤ f) :
  ∑' i, (f i - g i) = (∑' i, f i) - (∑' i, g i) :=
begin
  have h₃: ∑' i, (f i - g i) = ∑' i, (f i - g i + g i) - ∑' i, g i,
  { rw [ennreal.tsum_add, add_sub_self h₁]},
  have h₄:(λ i, (f i - g i) + (g i)) = f,
  { ext n, rw ennreal.sub_add_cancel_of_le (h₂ n)},
  rw h₄ at h₃, apply h₃,
end

end tsum

lemma ereal.coe_tsum_eq_tsum_coe (f : ℕ → ℝ≥0∞) : 
  (↑(∑' i, f i) : ereal) = ∑' i, f i := 
begin
  sorry
end 

lemma ereal.eq_neg_iff {a b : ereal} (ha : a ≠ ⊤) (h : a + b = 0) : a = -b :=
begin
  revert h,
  rcases b.cases with rfl | ⟨b, rfl⟩ | rfl,
  { rw neg_bot, 
    rcases a.cases with rfl | ⟨a, rfl⟩ | rfl; norm_num },
  { rcases a.cases with rfl | ⟨a, rfl⟩ | rfl,
    { norm_num },
    { rw [← coe_add, ← coe_zero, ereal.coe_eq_coe_iff, 
          add_eq_zero_iff_eq_neg],
      rintro rfl,
      exact coe_neg _ },
    { norm_num } },
  { norm_num }
end

-- lemma ereal.tsum_neg (f : ℕ → ereal) : - ∑' i, f i = ∑' i, - f i := 
-- begin
--   by_cases summable f,
--   { --have := summable_neg_iff h,
--     by_cases hsum : ∑' (i : ℕ), -f i = ⊤,
--     { sorry

--     },
--     { suffices : ∑' (i : ℕ), -f i + ∑' (i : ℕ), f i = 0,
--         symmetry,
--         apply ereal.eq_neg_iff hsum this,
--       rw ← tsum_add,
      
--        },
--   },
-- end

end ereal