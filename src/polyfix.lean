import polycodable

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
  { clear ih ht₂, simp [pfun.to_fun, eval_fix_fun] at fv, simp [pfun.to_fun, code_fix_time] at H,
    rcases H with ⟨t', ht', rfl⟩,
    cases fv with fv₁ fv₂,
    simp only [add_le_add_iff_right],
    have : ∃ t'', sum.inl t'' ∈ time_fix_fun c (x, 0),
    { use (c.time.to_fun (by rwa time_dom_eq_eval_dom) x), 
      simp [time_fix_fun], } }
end


private def c_invariant (c : code) (hc : c.eval.dom = set.univ) (v : ptree) (T M : ℕ) : Prop :=
  fix_bounded_terminates
    (pfun.to_fun (eval_fix_fun c) (by rwa eval_fix_fun_dom_eq_dom))
    (λ x, x.sizeof ≤ M) 
    T v

lemma time_bound_fix {c : code} {b₁ b₂ m : ℕ → ℕ} (hb₁ : time_bound c b₁)
  (hb₂ : ∀ x : ptree, c_invariant c (eval_dom_of_time_bound hb₁) x (b₂ x.sizeof) (m x.sizeof)) : time_bound c.fix (λ t, (b₁ $ m t) * (b₂ t) + 1) :=
begin
  intros n v hnv,
  have : (c.fix.time v).dom,
  { rw [time_dom_iff_eval_dom, code_fix_eval], simpa using dom_of_fix_bounded_terminates (hb₂ v), },
  rw part.dom_iff_mem at this, rcases this with ⟨t, ht⟩, use [t, ht],
  simp only [code_fix_time, part.mem_map_iff, part.map_eq_map] at ht, rcases ht with ⟨t', ht, rfl⟩, dsimp only,
  simp only [add_le_add_iff_right], -- Invariant: fix_bounded_terminates (pfun.to_fun ...) ... (b₂ x.sizeof) - t
  refine pfun.fix_induction_invariant (λ vt : ptree × ℕ, c_invariant c (eval_dom_of_time_bound hb₁) vt.1 ((b₂ v.sizeof) - vt.2) (m v.sizeof)) ht _ _ _,
  { simpa using hb₂ _, },
  { rintros ⟨x₁, t₁⟩ ⟨x₂, t₂⟩ hx₁ hx₂, dsimp only,
    simp [c_invariant], }
end

end time_bound_fix_lemma

#exit

lemma polytime_fix_bounded (p q : polynomial ℕ) (f : α → β ⊕ α) (g : α → β)
  (hf : ∀ x, g x ∈ fix_bounded_while f (λ x' : α, encode_sizeof x' ≤ q.eval (encode_sizeof x)) (p.eval (encode_sizeof x)) x) :
  polytime_fun f → polytime_fun g :=
begin
  rintro ⟨c, pc, s⟩,
  use code.fix c, split, swap,
  { intro x, simp only [part.eq_some_iff], rw code_fix_eq_pfun_fix' s, simpa using fix_eq_fix_bounded (hf x), },
  -- Max output value: q(x), max time per step: pc(q(x)), max time: p(x)pc(q(x))
end

-- lemma polytime_fix_bounded (p : polynomial ℕ) (f : α → β ⊕ α) (g : α → β)
--   (hf : ∀ x, g x ∈ fix_bounded_iter f (p.eval (encode_sizeof x)) x) 
--   (bg : ∃ C : ℕ, ∀ x, encode_sizeof (f x) ≤ (encode_sizeof x) + C) : polytime_fun f → polytime_fun g :=
-- begin
--   rintro ⟨c, pc, s⟩,
--   use code.fix c, split, swap,
--   { intro x, simp only [part.eq_some_iff], rw code_fix_eq_pfun_fix' s, simpa using fix_eq_fix_bounded (hf x), },
  
-- end

end poly
