import polyfix

variables {α : Type*}
def mk_fix_fun_of_iterate (f : α → α) (halt : α → Prop) [decidable_pred halt] :
  α → α ⊕ α :=
λ x, if halt x then sum.inl x else sum.inr (f x)

lemma polytime_fun.mk_fix_fun {α : Type*} [polycodable α] {f : α → α} (hf : polytime_fun f) {halt : α → Prop} [decidable_pred halt] (hhalt : polydecidable halt) :
  polytime_fun (mk_fix_fun_of_iterate f halt) :=
by { apply polytime_fun.ite hhalt, apply polytime_fun.sum_inl, apply polytime_fun.comp, apply polytime_fun.sum_inr, exact hf, }

open_locale classical

lemma fix_bounded_while_of_iterate (f : α → α) (halt : α → Prop) (start : α) (n : ℕ)
  (h₀ : halt (f^[n] start)) (h₁ : ∀ m < n, ¬halt (f^[m] start)) :
  fix_bounded_while (mk_fix_fun_of_iterate f halt) (λ x, ∃ i ≤ n, f^[i] start = x) (n + 1) start = 
  some (f^[n] start) :=
begin
  have trv_start : ∃ i, (i ≤ n) ∧ (f^[i] start = start) := ⟨0, zero_le', rfl⟩,
  induction n with n ih generalizing start,
  { simp only [id.def, function.iterate_zero] at h₀,
    simp [fix_bounded_while, h₀, trv_start, mk_fix_fun_of_iterate], },
  specialize ih (f start) (by simpa using h₀) _ ⟨0, zero_le', rfl⟩,
  { intros m hm, simpa using h₁ (m+1) (by simpa [nat.succ_eq_add_one]), },
  rw [fix_bounded_while],
  specialize h₁ 0 (by simp), simp at h₁,
  simp [trv_start, mk_fix_fun_of_iterate, h₁],
  simp [fix_bounded_while._match_1],
  apply fix_bounded_while_weaken _ rfl.le ih,
  rintros x ⟨i, H, hi⟩, use (i+1), split, { simpa [nat.succ_eq_add_one], }, simpa,
end

