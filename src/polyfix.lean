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

abbreviation encode_sizeof (x : α) := (polycodable.encode x).sizeof

-- lemma polytime_fix_bounded (p : polynomial ℕ) (f : α → β ⊕ α) (g : α → β)
--   (hf : ∀ x, g x ∈ fix_bounded_iter f (p.eval (encode_sizeof x)) x) : polytime_fun f → polytime_fun g :=

end poly
