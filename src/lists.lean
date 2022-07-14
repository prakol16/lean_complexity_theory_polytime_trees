import polyiterate
import data.list.basic

section list

def ptree_list_encoding_aux : polycodable (list ptree) :=
{ encode := ⟨ptree.equiv_list.symm, λ x y hxy, by simpa using hxy⟩,
  mem_poly' := by { convert polydecidable.true, ext x, simp, } }

local attribute [instance] ptree_list_encoding_aux

lemma encode_list_def (x : list ptree) : polycodable.encode x = ptree.equiv_list.symm x := rfl

lemma polytime_fun.head : polytime_fun (@list.head ptree _) :=
⟨code.left, polytime_left,
by { intro x, dunfold polycodable.encode, cases x; simp, refl, }⟩

lemma polytime_fun.tail : polytime_fun (@list.tail ptree) :=
⟨code.right, polytime_right,
by { intro x, dunfold polycodable.encode, cases x; simp, }⟩

lemma polytime_fun.cons : polytime_fun₂ (@list.cons ptree) :=
⟨code.id, polytime_id,
by { intro x, dunfold polycodable.encode, cases x; simp, }⟩

def foldl_step (f : ptree → ptree → ptree) (x : list ptree × ptree) : list ptree × ptree := (x.1.tail, f x.2 x.1.head)

lemma polytime_fun.foldl_step {f : ptree → ptree → ptree → ptree} (hf : polytime_fun₃ f) :
  polytime_fun₂ (λ d, foldl_step (f d)) :=
by { apply polytime_fun.pair, apply polytime_fun.comp, apply polytime_fun.tail, apply polytime_fun.comp, apply polytime_fun.prod_fst, apply polytime_fun.prod_snd, apply polytime_fun.comp₃ hf, apply polytime_fun.prod_fst, apply polytime_fun.comp, apply polytime_fun.prod_snd, apply polytime_fun.prod_snd, apply polytime_fun.comp, apply polytime_fun.head, apply polytime_fun.comp, apply polytime_fun.prod_fst, apply polytime_fun.prod_snd, }

lemma foldl_step_iterate (f : ptree → ptree → ptree) (i : ℕ) (l : list ptree) (acc : ptree) (hi : i ≤ l.length) :
  (foldl_step f)^[i] (l, acc) = (l.drop i, (l.take i).foldl f acc) :=
begin
  induction i with i ih generalizing acc l, { simp, },
  cases l with hd tl, { exfalso, simpa using hi, },
  specialize ih (f acc hd) tl _,
  { simpa [nat.succ_eq_add_one] using hi, }, { simp [foldl_step, ih], },
end

open_locale classical
noncomputable theory

def foldl_halt (x : list ptree × ptree) := x.1 = []

def foldl_fix_fun (f : ptree → ptree → ptree) := mk_fix_fun_of_iterate (foldl_step f) foldl_halt

lemma polytime_fun.foldl_fix_fun {f : ptree → ptree → ptree → ptree} (hf : polytime_fun₃ f) : polytime_fun₂ (λ d, foldl_fix_fun (f d)) :=
polytime_fun.mk_fix_fun (polytime_fun.foldl_step hf) (polydecidable_of_preimage_polytime (=[]) polytime_fun.prod_fst $ polydecidable.eq_const _)


lemma foldl_fix (f : ptree → ptree → ptree) (l : list ptree) (acc : ptree) :
  fix_bounded_while (foldl_fix_fun f) (λ x : list ptree × ptree, ∃ i ≤ l.length, l.drop i = x.1 ∧ (l.take i).foldl f acc = x.2) (l.length + 1) (l, acc) = some ([], l.foldl f acc) :=
begin
  have : nat.iterate (foldl_step f) l.length (l, acc) = ([], l.foldl f acc),
  { simp [foldl_step_iterate], },
  convert fix_bounded_while_of_iterate (foldl_step f) foldl_halt (l, acc) l.length _ _,
  { ext ⟨x₀, x₁⟩, simp [foldl_step_iterate], split,
    { rintro ⟨i, hi, h₀, h₁⟩, use [i, hi], simp [foldl_step_iterate, hi, h₀, h₁], },
    rintro ⟨i, hi, h⟩, use [i, hi], simpa [foldl_step_iterate, hi] using h, },
  { exact this.symm, }, { rw this, simp [foldl_halt], },
  intros m hm,
  simpa [foldl_step_iterate, le_of_lt hm, foldl_halt, list.drop_eq_nil_iff_le],
end

@[simp] lemma encode_sizeof_ptree (x : ptree) : encode_sizeof x = x.sizeof := rfl
@[simp] lemma encode_sizeof_nil : encode_sizeof ([] : list ptree) = 1 :=
by { dunfold encode_sizeof, simp [encode_list_def], }
@[simp] lemma encode_sizeof_cons (a : ptree) (b : list ptree) :
  encode_sizeof (a :: b) = 1 + encode_sizeof a + encode_sizeof b :=
by { dunfold encode_sizeof, simp [encode_list_def], }
lemma one_le_encode_sizeof {α : Type*} [polycodable α] (x : α) :
  1 ≤ encode_sizeof x :=
by { dunfold encode_sizeof, cases (polycodable.encode x); simp, linarith, }

@[simp] lemma encode_sizeof_append (a b : list ptree) :
  (encode_sizeof (a ++ b) : ℤ) = ((encode_sizeof a) : ℤ) + (encode_sizeof b) - 1 :=
by { induction a with hd tl ih, { simp, }, simp [ih], ring, }

lemma encode_sizeof_le_of_infix {a b : list ptree} (h : a <:+: b) :
  encode_sizeof a ≤ encode_sizeof b :=
begin
  rcases h with ⟨s, t, rfl⟩,
  have i₁ := one_le_encode_sizeof s, have i₂ := one_le_encode_sizeof t,
  zify at *, simp, linarith,
end

lemma len_le_encode_sizeof (a : list ptree) :
  a.length + 1 ≤ encode_sizeof a :=
by { induction a with hd tl ih, { simp, }, simp, linarith, }

def polysize_fun {α β : Type*} [polycodable α] [polycodable β] (f : α → β) : Prop :=
∃ p : polynomial ℕ, ∀ (n : ℕ) (x : α), encode_sizeof x ≤ n → encode_sizeof (f x) ≤ p.eval n

lemma polysize_of_polytime_fun {α β : Type*} [polycodable α] [polycodable β] (f : α → β) (hf : polytime_fun f) :
  polysize_fun f :=
begin
  obtain ⟨c, ⟨p, hp⟩, s⟩ := hf, use p, intros n x hx,
  obtain ⟨t, ht₀, ht₁⟩ := hp n (polycodable.encode x) hx,
  specialize s x, rw part.eq_some_iff at s,
  exact (eval_sizeof_le_time s ht₀).trans ht₁,
end


lemma polytime_fun.foldl' {f : ptree → ptree → ptree → ptree} {g : ptree → list ptree} {acc : ptree → ptree}
  (hf : polytime_fun₃ f) (hg : polytime_fun g) (hacc : polytime_fun acc) 
  (hsize : polysize_fun (λ xls : list ptree × ptree × ptree, xls.1.foldl (f xls.2.1) xls.2.2)) :
  polytime_fun (λ x, (@list.nil ptree, (g x).foldl (f x) (acc x))) :=
begin
  cases hsize with q hq,
  have := polytime_fix_bounded' (polynomial.monomial 1 1) (q + polynomial.monomial 1 1)
    (λ d, foldl_fix_fun (f d)) (λ d x, ([], x.1.foldl (f d) x.2)) _ _,
  { have := polytime_fun.comp₂ this polytime_fun.id (polytime_fun.pair hg hacc), exact this, },
  { rintros d ⟨l, s⟩, dsimp only,
    apply fix_bounded_while_weaken _ _ (foldl_fix (f d) l s),
    { rintros ⟨l', s'⟩, dsimp only, rintros ⟨i, H, rfl, rfl⟩, 
      specialize hq _ ⟨l.take i, d, s⟩ rfl.le, dsimp only at hq,
      simp, conv_rhs { rw [add_comm, add_assoc], }, apply le_add_of_nonneg_of_le, { exact zero_le', },
      mono,
      { linarith only [encode_sizeof_le_of_infix (l.drop_suffix i).is_infix], },
      refine hq.trans _, apply monotone_polynomial_nat, simp, linarith only [encode_sizeof_le_of_infix (l.take_prefix i).is_infix], },
    refine (len_le_encode_sizeof _).trans _, simp, linarith only, },
  { apply polytime_fun.foldl_fix_fun hf, }
end

open polycodable (encode)
variables {α β : Type*} [polycodable α] [polycodable β]
def polycodable.decode [nonempty α] : ptree → α :=
function.inv_fun (@encode α _)

@[simp] lemma polycodable.decode_encode (x : α) : @polycodable.decode _ _ ⟨x⟩ (encode x) = x :=
by { haveI : nonempty α := ⟨x⟩, exact function.left_inverse_inv_fun (function.embedding.injective _) x }

lemma polytime_fun.polydecode [nonempty α] : polytime_fun (@polycodable.decode α _ _) :=
begin
  apply polytime_fun.decode,
  convert_to polytime_fun (λ x : ptree, if x ∈ set.range (@encode α _) then x else (encode $ classical.arbitrary α)),
  { ext x, split_ifs with h; simp [polycodable.decode],
    { exact function.inv_fun_eq h }, { exact function.inv_fun_neg h, }, },
  exact polytime_fun.ite (mem_poly α) polytime_fun.id (polytime_fun.const _),
end

lemma foldl_encode_comm (f : α → ptree → α) (acc : α) (l : list ptree) :
  encode (l.foldl f acc) = l.foldl (λ a x, encode $ f (@polycodable.decode _ _ ⟨acc⟩ a) x) (encode acc) :=
begin
  induction l with hd tl ih generalizing acc, { simp, },
  simp [ih],
end

lemma polytime_fun.foldl 
  {f : α → β → ptree → β} {g : α → list ptree} {acc : α → β}
  (hf : polytime_fun₃ f) (hg : polytime_fun g) (hacc : polytime_fun acc)
  (hsize : polysize_fun (λ xls : list ptree × α × β, xls.1.foldl (f xls.2.1) xls.2.2)) :
  polytime_fun (λ x, (g x).foldl (f x) (acc x)) :=
begin
  change polytime_fun (λ x, (@list.nil ptree, (g x).foldl (f x) (acc x)).snd),
  apply polytime_fun.comp polytime_fun.prod_snd, swap, { apply_instance, /- For some reason Lean decided not to infer this instance -/ },
  apply polytime_fun.decode, simp [function.comp],
  sorry,
  -- convert_to polytime_fun (λ x, (@list.nil ptree, (g x).foldl )) 
end

lemma list.all_eq_foldl {α : Type*} (P : α → bool) (l : list α) :
  l.all P = l.foldl (λ r a, r && P a) tt :=
begin
  have : ∀ l : list α, l.foldl (λ r a, r && P a) ff = ff,
  { clear l, intro l, induction l; simp [*], },
  induction l with hd tl ih, { simp, }, cases h : P hd; simp [*],
end

lemma polytime_fun.list_all {P : ptree → bool} (hP : polytime_fun P) :
  polytime_fun (λ l : list ptree, l.all P) :=
begin
  convert_to polytime_fun (λ l : list ptree, l.foldl (λ r a, r && P a) tt),
  { ext l, exact list.all_eq_foldl _ _, },

end

#check bool.band_comm
#check list.foldr_eq_of_comm'

-- local attribute [-instance] ptree_list_encoding_aux

end list
