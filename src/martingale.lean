import measure_theory.function.conditional_expectation
import probability_theory.notation

noncomputable theory
open_locale classical measure_theory nnreal ennreal topological_space probability_theory

namespace measure_theory

/-- A `filtration` on measurable space `α` with σ-algebra `m` is a monotone 
sequence of of sub-σ-algebras of `m`. -/
structure filtration (α ι : Type*) [preorder ι] (m : measurable_space α) :=
(seq : ι → measurable_space α)
(mono : monotone seq) (le : ∀ i : ι, seq i ≤ m)

instance {α ι : Type*} [preorder ι] {m : measurable_space α} : 
  has_coe_to_fun (filtration α ι m) (λ _, ι → measurable_space α) := 
⟨λ f, f.seq⟩

open topological_space

variables {α β ι : Type*} {m : measurable_space α} [measurable_space β]
variables {E : Type*} [normed_group E] [measurable_space E]  
  [second_countable_topology E] [normed_space ℝ E] [complete_space E] [borel_space E]

section

variables [preorder ι]

lemma measurable_set_of_filtration {f : filtration α ι m} {s : set α} {i : ι}
  (hs : measurable_set[f i] s) : measurable_set[m] s :=
f.le i s hs

/-- A measure is σ-finite with respect to filtration if it is σ-finite with respect 
to all the sub-σ-algebra of the filtration. -/
class sigma_finite_filtration (μ : measure α) (f : filtration α ι m) : Prop :=
(sigma_finite : ∀ ⦃i : ι⦄, @sigma_finite α (f i) (μ.trim (f.le i)))

instance sigma_finite_of_sigma_finite_filtration (μ : measure α) (f : filtration α ι m)
  [hf : sigma_finite_filtration μ f] (i : ι) : 
  @sigma_finite α (f i) (μ.trim (f.le i)) := 
by apply hf.sigma_finite -- can't exact here

/-- A sequence of functions `u` is adapted to a filtration `f` if for all `i`, 
`u i` is `f i`-measurable. -/
def adapted (f : filtration α ι m) (u : ι → α → β) : Prop := 
∀ ⦃i : ι⦄, measurable[f i] (u i)

namespace filtration

/-- Given a sequence of functions, the natural filtration is the smallest sequence 
of σ-algebras such that that sequence of functions is measurable with respect to 
the filtration. -/
def natural (u : ι → α → β) (hum : ∀ i, measurable (u i)) : filtration α ι m := 
{ seq := λ i, ⨆ j ≤ i, measurable_space.comap (u j) infer_instance,
  mono := λ i j hij, bsupr_le_bsupr' $ λ k hk, le_trans hk hij,
  le := λ i, bsupr_le (λ j hj s hs, let ⟨t, ht, ht'⟩ := hs in ht' ▸ hum j ht) }

-- move -- does this exist?
lemma measurable_le {m m0 : measurable_space α} (hm : m ≤ m0) {f : α → β}
  (hf : measurable[m] f) : measurable[m0] f :=
λ s hs, hm _ (hf hs)

lemma adapted_natural {u : ι → α → β} (hum : ∀ i, measurable[m] (u i)) : 
  adapted (natural u hum) u := 
λ i, measurable_le (le_bsupr_of_le i (le_refl i) (le_refl _)) (λ s hs, ⟨s, hs, rfl⟩)

end filtration

def is_martingale (μ : measure α) (f : filtration α ι m) (u : ι → Lp E 1 μ) : Prop :=
∀ ⦃i j : ι⦄, i ≤ j → ∀ ⦃s : set α⦄, measurable_set[f i] s →
  ∫ x in s, u i x ∂μ = ∫ x in s, u j x ∂μ

def is_submartingale [has_le E] 
  (μ : measure α) (f : filtration α ι m) (u : ι → Lp E 1 μ) : Prop :=
∀ ⦃i j : ι⦄, i ≤ j → ∀ ⦃s : set α⦄, measurable_set[f i] s →
  ∫ x in s, u i x ∂μ ≤ ∫ x in s, u j x ∂μ

def is_supermartingale [has_le E] 
  (μ : measure α) (f : filtration α ι m) (u : ι → Lp E 1 μ) : Prop :=
∀ ⦃i j : ι⦄, i ≤ j → ∀ ⦃s : set α⦄, measurable_set[f i] s →
  ∫ x in s, u j x ∂μ ≤ ∫ x in s, u i x ∂μ

variables {μ : measure α} {f : filtration α ι m} 

section

variables {u : ι → Lp E 1 μ}

lemma is_martingale.is_submartingale [preorder E] (hu : is_martingale μ f u) : 
  is_submartingale μ f u :=
λ _ _ hij _ hs, (hu hij hs).le

lemma is_martingale.is_supermartingale [preorder E] (hu : is_martingale μ f u) : 
  is_supermartingale μ f u :=
λ _ _ hij _ hs, (hu hij hs).ge

lemma is_martingale_iff [partial_order E] :
  is_martingale μ f u ↔ is_submartingale μ f u ∧ is_supermartingale μ f u := 
⟨λ hu, ⟨hu.is_submartingale, hu.is_supermartingale⟩, 
 λ ⟨hsub, hsup⟩ _ _ hij _ hs, le_antisymm (hsub hij hs) (hsup hij hs)⟩

lemma condexp_eq_of_is_martingale 
  [sigma_finite_filtration μ f] (hum : is_martingale μ f u) 
  {i j : ι} (hij : i ≤ j) (huim : measurable[f i] (u i)) : 
  u i =ᵐ[μ] μ[u j | f.le i] := 
begin
  have hui : ∀ i, integrable (u i) μ,
  { intro i,
    erw [← mem_ℒp_one_iff_integrable, ← Lp.mem_Lp_iff_mem_ℒp],
    exact set_like.coe_mem _ },
  refine ae_eq_condexp_of_forall_set_integral_eq _ (hui j) _ _ _,
  { exact λ s hs hlt, (hui i).integrable_on },
  { exact λ s hs hlt, hum hij hs },
  { exact measurable.ae_measurable' huim } 
end

-- The following lemma compiles but crashes lean sometimes.

-- lemma is_submartingale.neg [preorder E] [covariant_class E E (+) (≤)]
--   (hu : is_submartingale μ f u) : 
--   is_supermartingale μ f (-u) :=
-- begin
--   intros _ _ hij _ hs,
--   rw [(_ : ∫ x in s, (-u) j x ∂μ = ∫ x in s, -u j x ∂μ), 
--       (_ : ∫ x in s, (-u) i x ∂μ = ∫ x in s, -u i x ∂μ), 
--       integral_neg, integral_neg, neg_le_neg_iff],
--   { exact hu hij hs },
--   { rw set_integral_congr_ae (measurable_set_of_filtration hs),
--     filter_upwards [Lp.coe_fn_neg (u i)],
--     intros, assumption },
--   { rw set_integral_congr_ae (measurable_set_of_filtration hs),
--     filter_upwards [Lp.coe_fn_neg (u j)],
--     intros, assumption },
-- end

-- lemma is_supermartingale.neg [preorder E] [covariant_class E E (+) (≤)]
--   (hu : is_supermartingale μ f u) : 
--   is_submartingale μ f (-u) :=
-- begin
--   intros _ _ hij _ hs,
--   rw [(_ : ∫ x in s, (-u) j x ∂μ = ∫ x in s, -u j x ∂μ), 
--       (_ : ∫ x in s, (-u) i x ∂μ = ∫ x in s, -u i x ∂μ), 
--       integral_neg, integral_neg, neg_le_neg_iff],
--   { exact hu hij hs },
--   { rw set_integral_congr_ae (measurable_set_of_filtration hs),
--     filter_upwards [Lp.coe_fn_neg (u i)],
--     intros, assumption },
--   { rw set_integral_congr_ae (measurable_set_of_filtration hs),
--     filter_upwards [Lp.coe_fn_neg (u j)],
--     intros, assumption },
-- end

end

/-- A stopping time with respect to some filtration `f` is a function 
`τ` such that for all `i`, the preimage of `{j | j ≤ i}` along `τ` is measurable 
with respect to `f i`.

Intuitively, the stopping time `τ` describes some stopping rule such that at time 
`i`, we may determine it with the information we have at time `i`. -/
def is_stopping_time (f : filtration α ι m) (τ : α → ι) :=
∀ i : ι, measurable_set[f i] $ {x | τ x ≤ i}

section

lemma is_stopping_time.measurable_set_eq
  {f : filtration α ℕ m} {τ : α → ℕ} (hτ : is_stopping_time f τ) (i : ℕ) : 
  measurable_set[f i] $ {x | τ x = i} :=
begin
  cases i,
  { convert (hτ 0), 
    simp only [set.set_of_eq_eq_singleton, le_zero_iff] },
  { rw (_ : {x | τ x = i + 1} = {x | τ x ≤ i + 1} \ {x | τ x ≤ i}),
    { exact @measurable_set.diff _ (f (i + 1)) _ _ (hτ (i + 1)) 
        (f.mono (nat.le_succ _) _ (hτ i)) },
    { ext, simp only [set.mem_diff, not_le, set.mem_set_of_eq],
      split,
      { intro h, simp [h] },
      { rintro ⟨h₁, h₂⟩,
        linarith } } }
end

lemma is_stopping_time_of_measurable_set_eq
  {f : filtration α ℕ m} {τ : α → ℕ} (hτ : ∀ i, measurable_set[f i] $ {x | τ x = i}) : 
  is_stopping_time f τ :=
begin
  intro i,
  rw show {x | τ x ≤ i} = ⋃ k ≤ i, {x | τ x = k}, by { ext, simp },
  refine @measurable_set.bUnion _ _ (f i) _ _ (set.countable_encodable _) (λ k hk, _),
  exact f.mono hk _ (hτ k),
end

end

lemma is_stopping_time_const {f : filtration α ι m} (i : ι) : 
  is_stopping_time f (λ x, i) :=
λ j, by simp

end

lemma is_stopping_time.max [linear_order ι] {f : filtration α ι m} {τ π : α → ι}
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  is_stopping_time f (λ x, max (τ x) (π x)) :=
begin
  intro i, 
  simp_rw [max_le_iff, set.set_of_and],
  exact @measurable_set.inter _ (f i) _ _ (hτ i) (hπ i),
end

lemma is_stopping_time.min [linear_order ι] {f : filtration α ι m} {τ π : α → ι}
  (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) :
  is_stopping_time f (λ x, min (τ x) (π x)) :=
begin
  intro i, 
  simp_rw [min_le_iff, set.set_of_or],
  exact @measurable_set.union _ (f i) _ _ (hτ i) (hπ i),
end

lemma is_stopping_time.add_const
  [add_group ι] [preorder ι] [covariant_class ι ι (function.swap (+)) (≤)] 
  [covariant_class ι ι (+) (≤)] 
  {f : filtration α ι m} {τ : α → ι} (hτ : is_stopping_time f τ) {i : ι} (hi : 0 ≤ i) :
  is_stopping_time f (λ x, τ x + i) :=
begin
  intro j,
  simp_rw [← le_sub_iff_add_le],
  exact f.mono (sub_le_self j hi) _ (hτ (j - i)),
end

section 

variables [preorder ι] {f : filtration α ι m}

/-- Given a map `u : ι → α → E`, its stopped process with respect to the stopping 
time `τ` is the map `(i, x) ↦ u (min i (τ x)) x`. 

Intuitively, the stopped process stop evolving once the stopping time has occured. -/
def is_stopping_time.stopped_process {α ι : Type*} [linear_order ι] 
  {m : measurable_space α} (f : filtration α ι m) (u : ι → α → E) 
  {τ : α → ι} (hτ : is_stopping_time f τ) : ι → α → E :=
λ i x, u (min i (τ x)) x

def is_stopping_time.measurable_space (f : filtration α ι m)
  {τ : α → ι} (hτ : is_stopping_time f τ) : measurable_space α :=
{ measurable_set' := λ s, ∀ i : ι, measurable_set[f i] (s ∩ {x | τ x ≤ i}),
    measurable_set_empty := 
      λ i, (set.empty_inter {x | τ x ≤ i}).symm ▸ @measurable_set.empty _ (f i),
    measurable_set_compl := λ s hs i, 
      begin
        rw (_ : sᶜ ∩ {x | τ x ≤ i} = (sᶜ ∪ {x | τ x ≤ i}ᶜ) ∩ {x | τ x ≤ i}),
        { refine @measurable_set.inter _ (f i) _ _ _ _,
          { rw ← set.compl_inter,
            exact @measurable_set.compl _ _ (f i) (hs i) },
          { exact hτ i} },
        { rw set.union_inter_distrib_right, 
          simp only [set.compl_inter_self, set.union_empty] }
      end,
    measurable_set_Union := λ s hs i,
      begin
        rw forall_swap at hs,
        rw set.Union_inter,
        exact @measurable_set.Union _ _ (f i) _ _ (hs i),
      end }

lemma is_stopping_time.measurable_space_le [encodable ι] (f : filtration α ι m)
  {τ : α → ι} (hτ : is_stopping_time f τ) : 
  hτ.measurable_space f ≤ m :=
begin
  intros s hs,
  change ∀ i, measurable_set[f i] (s ∩ {x | τ x ≤ i}) at hs,
  rw (_ : s = ⋃ i, s ∩ {x | τ x ≤ i}), 
  { exact measurable_set.Union (λ i, f.le i _ (hs i)) },
  { ext x, split; rw set.mem_Union, 
    { exact λ hx, ⟨τ x, hx, le_refl _⟩ },
    { rintro ⟨_, hx, _⟩,
      exact hx } }
end

-- instance is_stopping_time.sigma_finite 
--   [encodable ι] {μ : measure α} [sigma_finite_filtration μ f] 
--   (f : filtration α ι m) {τ : α → ι} (hτ : is_stopping_time f τ) (i : ι) : 
--   @sigma_finite α (hτ.measurable_space f) (μ.trim (hτ.measurable_space_le f)) :=
-- begin
--   sorry
-- end

end

section

variables [encodable ι] [linear_order ι] {f : filtration α ι m} [has_le E] 
  {μ : measure α} [sigma_finite_filtration μ f]

-- Is this the correct formulation 
-- lemma foo {u : ι → Lp E 1 μ} (hu : is_supermartingale μ f u) {τ π : α → ι} 
--   (hτ : is_stopping_time f τ) (hπ : is_stopping_time f π) (i : ι) :
--   μ[hτ.stopped_process f (λ i, u i) i | hπ.measurable_space_le f] = 
--   (hτ.max hπ).stopped_process f (λ i, u i) i := 
-- begin
--   sorry
-- end

end

end measure_theory