import polycodable
import npolynomial

variables {α β : Type*}

def fix_bounded_while (f : α → β ⊕ α) (P : α → Prop) [decidable_pred P] : ℕ → α → option β
| 0 x := none
| (n + 1) x := if P x then match f x with
  | (sum.inl y) := some y
  | (sum.inr x') := fix_bounded_while n x'
end else none

def fix_bounded_terminates (f : α → β ⊕ α) (P : α → Prop) [decidable_pred P] (i : ℕ) (x : α) : Prop :=
(fix_bounded_while f P i x).is_some

lemma not_fix_bounded_terminates_zero (f : α → β ⊕ α) (P : α → Prop) [decidable_pred P] (x : α) :
  ¬fix_bounded_terminates f P 0 x := by trivial

lemma fix_bounded_terminates_iff (f : α → β ⊕ α) (P : α → Prop) [decidable_pred P] (i : ℕ) (x : α) :
  (fix_bounded_terminates f P (i+1) x) ↔ P x ∧ (∀ x', f x = sum.inr x' → fix_bounded_terminates f P i x') :=
begin
  simp only [fix_bounded_terminates, fix_bounded_while],
  split_ifs with H, swap, { simp [H], },
  cases hf : f x; simp [fix_bounded_while, H],
end

private lemma fix_bounded_while_weaken_prop {f : α → β ⊕ α} {P Q : α → Prop} {n : ℕ} {x₀ : α} {y : β} [decidable_pred P] [decidable_pred Q]
  (h : ∀ x, P x → Q x) (hb : y ∈ fix_bounded_while f P n x₀) : y ∈ fix_bounded_while f Q n x₀ :=
begin
  induction n with n ih generalizing x₀,
  { contradiction, },
  simp [fix_bounded_while] at ⊢ hb, 
  split_ifs at hb with H, swap, { contradiction, }, simp [h _ H],
  cases (f x₀) with v; simp [fix_bounded_while] at ⊢ hb,
  { assumption, }, { exact ih hb, },
end

private lemma fix_bounded_while_weaken_ind {f : α → β ⊕ α} {P : α → Prop} {m n : ℕ} {x₀ : α} {y : β} [decidable_pred P]
  (hmn : m ≤ n) (hb : y ∈ fix_bounded_while f P m x₀) : y ∈ fix_bounded_while f P n x₀ :=
begin
  induction n with n ih generalizing m x₀,
  { simp at hmn, subst hmn, contradiction, },
  cases m, { contradiction, },
  rw nat.succ_le_succ_iff at hmn,
  simp [fix_bounded_while] at ⊢ hb,
  split_ifs at ⊢ hb, swap, { contradiction, },
  cases (f x₀) with v; simp [fix_bounded_while] at ⊢ hb,
  { assumption, }, { exact ih hmn hb, }
end

lemma fix_bounded_while_weaken {f : α → β ⊕ α} {P Q : α → Prop} {m n : ℕ} {x₀ : α} {y : β} [decidable_pred P] [decidable_pred Q]
  (hp : ∀ x, P x → Q x) (hmn : m ≤ n) (hb : y ∈ fix_bounded_while f P m x₀) : y ∈ fix_bounded_while f Q n x₀ :=
fix_bounded_while_weaken_ind hmn (fix_bounded_while_weaken_prop hp hb)

lemma fix_bounded_terminates_weaken {f : α → β ⊕ α} {P Q : α → Prop} {m n : ℕ} {x₀ : α} [decidable_pred P] [decidable_pred Q]
  (hp : ∀ x, P x → Q x) (hmn : m ≤ n) (hb : fix_bounded_terminates f P m x₀) : fix_bounded_terminates f Q n x₀ :=
begin
  simp only [fix_bounded_terminates, option.is_some_iff_exists] at ⊢ hb,
  rcases hb with ⟨y, hy⟩, use y, exact fix_bounded_while_weaken hp hmn hy,
end

lemma fix_eq_fix_bounded {f : α → β ⊕ α} {P : α → Prop} [decidable_pred P] {x : α} {y : β} {i : ℕ}
  (h : y ∈ fix_bounded_while f P i x) : y ∈ pfun.fix (f : α →. β ⊕ α) x :=
begin
  induction i with i ih generalizing x,
  { simp [fix_bounded_while] at h, contradiction, },
  simp only [fix_bounded_while] at h, split_ifs at h with _, swap, { trivial, },
  cases H : f x with vl vr,
  { apply pfun.fix_stop, simp [fix_bounded_while, H] at h ⊢, exact h.symm, },
  specialize ih (by simpa [fix_bounded_while, H, ← option.mem_def] using h),
  rw [@comm _ (=), ← part.mem_some_iff, ← pfun.coe_val] at H,
  rwa pfun.fix_fwd _ _ H,
end

lemma dom_of_fix_bounded_terminates {f : α → β ⊕ α} {P : α → Prop} [decidable_pred P] {x : α} {i : ℕ}
  (h : fix_bounded_terminates f P i x) : (pfun.fix (f : α →. β ⊕ α) x).dom :=
begin
  rw [fix_bounded_terminates, option.is_some_iff_exists] at h, rcases h with ⟨y, hy⟩,
  rw part.dom_iff_mem, use [y, fix_eq_fix_bounded hy],
end

section poly
variables [polycodable α] [polycodable β]
open polycodable (encode)

lemma frespects_once_code_fix_pfun_fix {f : α →. β ⊕ α} {c : code} (hfc : ∀ x, c.eval (encode x) =  (f x).map encode) :
  pfun.frespects_once' f (eval_fix_fun c) encode encode :=
begin
  intro a, split,
  { intro h, simpa [eval_fix_fun, hfc] using h, }, split,
  { intros a' ha', simp only [eval_fix_fun, part.mem_map_iff],
    use (encode (ff, a')), split,
    { rw ← part.eq_some_iff at ha', simp [hfc, ha'], refl, }, split, },
  intros b hb, simp [eval_fix_fun], use encode (tt, b), split,
  { rw ← part.eq_some_iff at hb, simp [hfc, hb], refl, }, split; refl,
end

lemma code_fix_eq_pfun_fix {f : α →. β ⊕ α} {c : code} (hfc : ∀ x, c.eval (encode x) =  (f x).map encode) (x : α) :
  c.fix.eval (encode x) = (pfun.fix f x).map encode :=
(pfun.eq_val_of_frespects_once' (frespects_once_code_fix_pfun_fix hfc) x).symm

lemma code_fix_eq_pfun_fix' {f : α → β ⊕ α} {c : code} (hfc : ∀ x, c.eval (encode x) = part.some (encode $ f x)) (x : α) :
  c.fix.eval (encode x) = (pfun.fix (f : α →. β ⊕ α) x).map encode :=
by { apply code_fix_eq_pfun_fix, simp [hfc], }

lemma eval_fix_fun_dom_eq_dom {c : code} : pfun.dom (eval_fix_fun c) = c.eval.dom :=
by simp [pfun.dom]

abbreviation encode_sizeof (x : α) := (encode x).sizeof

section time_bound_fix_lemma

lemma part.get_iff_mem_prop {δ : Type*} (x : part δ) (h : x.dom) (P : δ → Prop) :
  P (x.get h) ↔ ∃ v ∈ x, P v :=
by { split, { intro H, use x.get h, exact ⟨part.get_mem _, H⟩, }, rintro ⟨v, hv, hP⟩, rwa part.get_eq_of_mem hv h, }

lemma time_bound_of_fix_bounded_terminates {c : code} {x : ptree}
  (hc : c.eval.dom = set.univ) {T J : ℕ}
  (ht : fix_bounded_terminates (pfun.to_fun (eval_fix_fun c) (by rwa eval_fix_fun_dom_eq_dom))
    (λ x', (c.time.to_fun (by rwa time_dom_eq_eval_dom) x') ≤ T) J x) :
  ∃ t ∈ c.fix.time x, t ≤ J * T + 1 :=
begin
  induction J with j ih generalizing x,
  { exfalso, exact not_fix_bounded_terminates_zero _ _ _ ht, },
  have : (c.fix.time x).dom,
  { rw [time_dom_iff_eval_dom, code_fix_eval], simpa using dom_of_fix_bounded_terminates ht,},
  rw part.dom_iff_mem at this, cases this with t H, use [t, H],
  rw fix_bounded_terminates_iff at ht, cases ht with ht₁ ht₂,
  cases fv : pfun.to_fun (eval_fix_fun c) (by rwa eval_fix_fun_dom_eq_dom) x with y x',
  all_goals
  { simp [pfun.to_fun, code_fix_time] at H,
    rcases H with ⟨t', ht', rfl⟩,
    have ht₁' : ∃ t₁ ∈ c.time x, t₁ ≤ T := by { rw ← part.get_iff_mem_prop, exact ht₁, },
    clear ht₁, rcases ht₁' with ⟨t₁, ht₁, t₁_le⟩,
    simp only [add_le_add_iff_right], },
  { clear ih ht₂, simp [pfun.to_fun, eval_fix_fun] at fv, cases fv with fv₁ fv₂,
    have : (c.eval x).dom, { change x ∈ c.eval.dom, rw hc, trivial, }, rw part.dom_iff_mem at this, cases this with fv hfv,
    rw part.get_eq_of_mem hfv _ at fv₁ fv₂,
    have : sum.inl t₁ ∈ time_fix_fun c (x, 0),
    { simp [time_fix_fun], use [t₁, ht₁, fv, hfv], simp [fv₁], },
    cases part.mem_unique (pfun.fix_stop _ this) ht', refine t₁_le.trans _, rw nat.succ_eq_add_one, nlinarith only, },
  specialize ht₂ _ fv, specialize ih ht₂,
  simp [pfun.to_fun, eval_fix_fun] at fv, cases fv with fv₁ fv₂,
  have : (c.eval x).dom, { change x ∈ c.eval.dom, rw hc, trivial, }, rw part.dom_iff_mem at this, cases this with fv hfv,
  rw part.get_eq_of_mem hfv _ at fv₁ fv₂,
  have := time_fix_spec hfv fv₁ ht₁, subst fv₂, rw code_fix_time at this,
  rw ← part.eq_some_iff at ht', rw [ht', @comm _ (=)] at this, simp [part.eq_some_iff] at this,
  rcases this with ⟨t, ht, Ht⟩, rcases ih with ⟨t, ht₂, Ht₂⟩, cases part.mem_unique ht ht₂,
  suffices : t' + 1 ≤ j * T + T + 1, { simpa [nat.succ_mul] using this, },
  rw ← Ht, nlinarith only [Ht₂, t₁_le],
end

lemma time_bound_fix {c : code} {b₁ b₂ m : ℕ → ℕ} (hb₁ : time_bound c b₁) (mono₁ : monotone b₁) (mono₂ : monotone b₂) (mono₃ : monotone m)
  (hb₂ : ∀ x : ptree, fix_bounded_terminates
    (pfun.to_fun (eval_fix_fun c) (by rw [eval_fix_fun_dom_eq_dom, eval_dom_of_time_bound hb₁]))
    (λ x', x'.sizeof ≤ m x.sizeof)
    (b₂ x.sizeof) x) :
  time_bound c.fix (λ t, (b₁ (m t)) * (b₂ t) + 1) :=
begin
  intros n v hnv, specialize hb₂ v, dsimp only, rw mul_comm,
  apply time_bound_of_fix_bounded_terminates, swap, { rw [eval_dom_of_time_bound hb₁], },
  refine fix_bounded_terminates_weaken _ (mono₂ hnv) hb₂,
  intros x hx, specialize hb₁ (m v.sizeof) _ hx, rcases hb₁ with ⟨t, H, ht⟩, 
  rw ← part.eq_some_iff at H,
  simp [pfun.to_fun, H], exact ht.trans (mono₁ (mono₃ hnv)),
end

end time_bound_fix_lemma

-- TODO: This is currently very ugly
lemma fix_bounded_terminates_norm_code_aux {f : α → β ⊕ α} {c : code} (hc : ∀ x : α, c.eval (encode x) = part.some (encode $ f x)) (hd : c.eval.dom = set.univ)
  (P : ptree → Prop) [decidable_pred P] (i : ℕ) (x : α) :
  fix_bounded_terminates (pfun.to_fun (eval_fix_fun c) (by rw [eval_fix_fun_dom_eq_dom, hd])) P i (encode x) ↔
  fix_bounded_terminates f (λ y, P (encode y)) i x :=
begin
  induction i with i ih generalizing x, { split; intro; contradiction, },
  simp [fix_bounded_terminates_iff], intro _,
  split,
  { intros h x' hx', specialize h (encode x') _, 
    { simp [pfun.to_fun, hc, hx'], split; trivial, },
    exact (ih x').mp h, },
  { intros h x' hx', simp [pfun.to_fun, hc] at hx',
    cases H : f x with val, { exfalso, cases hx' with l, rw H at l, contradiction, },
    rw H at hx', have : x' = encode val := hx'.2, subst this,
    rw ih, exact h _ H, }
end

lemma fix_bounded_terminates_norm_code {f : α → β ⊕ α} (hf : polytime_fun f) (P : ptree → ptree → Prop) [decidable_rel P] (i : ptree → ℕ) 
  (start₀ : ∀ x, P x x) (start₁ : ∀ x, 0 < i x) :
  (∀ (x : ptree), fix_bounded_terminates (pfun.to_fun (eval_fix_fun hf.norm_code) (by rw [eval_fix_fun_dom_eq_dom, hf.norm_code_dom])) (P x) (i x) x) ↔
  ∀ (x : α), fix_bounded_terminates f (λ y, P (encode x) (encode y)) (i (encode x)) x :=
begin
  split,
  { intros h x, rw ← fix_bounded_terminates_norm_code_aux hf.norm_code_eval, { exact h _, }, },
  intros h x,
  by_cases H : x ∈ set.range (@encode α _),
  { rcases H with ⟨v, rfl⟩, rw fix_bounded_terminates_norm_code_aux hf.norm_code_eval, exact h _, },
  specialize start₀ x, specialize start₁ x, cases (i x), { exfalso, simpa using start₁, },
  rw fix_bounded_terminates_iff, refine ⟨start₀, _⟩,
  intros x' h₂, exfalso, simpa [pfun.to_fun, hf.norm_code_invalid H] using h₂,
end

lemma polytime_fix_bounded_aux (p q : polynomial ℕ) (hpq₀ : ∀ n, 0 < p.eval n) (hpq₁ : ∀ n, n ≤ q.eval n) (f : α → β ⊕ α) (g : α → β)
  (hg : ∀ x, g x ∈ fix_bounded_while f (λ x' : α, encode_sizeof x' ≤ q.eval (encode_sizeof x)) (p.eval (encode_sizeof x)) x)
  (hf : polytime_fun f) : polytime_fun g :=
begin
  use code.fix hf.norm_code, split, swap,
  { intro x, simp only [part.eq_some_iff, ite_eval], rw code_fix_eq_pfun_fix' hf.norm_code_eval, simpa using fix_eq_fix_bounded (hg x), },
  rcases hf.polytime_norm_code with ⟨pc, hpc⟩,
  use (pc.comp q) * p + 1,
  { simp,
    apply time_bound_fix hpc (monotone_polynomial_nat pc) (monotone_polynomial_nat p) (monotone_polynomial_nat q),
    rw fix_bounded_terminates_norm_code hf, 
    { intro x, simp only [fix_bounded_terminates, option.is_some_iff_exists], use (g x),
      exact hg x, },
    { intro x, apply hpq₁, },
    intro, apply hpq₀, },
end

lemma polytime_fix_bounded (p q : polynomial ℕ) (f : α → β ⊕ α) (g : α → β)
  (hg : ∀ x, g x ∈ fix_bounded_while f (λ x' : α, encode_sizeof x' ≤ q.eval (encode_sizeof x)) (p.eval (encode_sizeof x)) x)
  (hf : polytime_fun f) : polytime_fun g :=
begin
  apply polytime_fix_bounded_aux (p+1) (q+polynomial.monomial 1 1) _ _ f g _ hf,
  { intro n, simp, },
  { intro n, simp, },
  intro x, apply fix_bounded_while_weaken _ _ (hg x),
  { intros x h, refine h.trans _, simp, },
  { simp, },
end

end poly
