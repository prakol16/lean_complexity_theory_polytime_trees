import polycodable

variables {α β : Type*}
def fix_bounded_iter (f : α → β ⊕ α) : ℕ → α → option β
| 0 x := none
| (n + 1) x := match f x with
  | (sum.inl y) := some y
  | (sum.inr x') := fix_bounded_iter n x'
end

lemma fix_eq_fix_bounded {f : α → β ⊕ α} {x : α} {y : β} {i : ℕ}
  (h : y ∈ fix_bounded_iter f i x) : y ∈ pfun.fix (f : α →. β ⊕ α) x :=
begin
  induction i with i ih generalizing x,
  { simp [fix_bounded_iter] at h, contradiction, },
  cases H : f x with vl vr,
  { apply pfun.fix_stop, simp [fix_bounded_iter, H] at h ⊢, exact h.symm, },
  specialize ih (by simpa [fix_bounded_iter, H, ← option.mem_def] using h),
  rw [@comm _ (=), ← part.mem_some_iff, ← pfun.coe_val] at H,
  rwa pfun.fix_fwd _ _ H,
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

abbreviation encode_sizeof (x : α) := (encode x).sizeof

lemma polytime_fix_bounded (p : polynomial ℕ) (f : α → β ⊕ α) (g : α → β)
  (hf : ∀ x, g x ∈ fix_bounded_iter f (p.eval (encode_sizeof x)) x) 
  (bg : ∃ C : ℕ, ∀ x, encode_sizeof (f x) ≤ (encode_sizeof x) + C) : polytime_fun f → polytime_fun g :=
begin
  rintro ⟨c, pc, s⟩,
  use code.fix c, split, swap,
  { intro x, simp only [part.eq_some_iff], rw code_fix_eq_pfun_fix' s, simpa using fix_eq_fix_bounded (hf x), },
  
end

end poly
