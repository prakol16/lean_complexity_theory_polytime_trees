import polyiterate
import data.list.basic

section list

def ptree_list_encoding_aux : polycodable (list ptree) :=
{ encode := ⟨ptree.equiv_list.symm, λ x y hxy, by simpa using hxy⟩,
  mem_poly' := by { convert polydecidable.true, ext x, simp, } }

local attribute [instance] ptree_list_encoding_aux
/--
polytime fix:
If a function increases size by at most a constant and is applied polynomially
many times, it runs in polynomial time.

Pf: Say it takes input size x --> x + C
Time:
p(x) + p(x+C) + p(x+2C) + ... + p(x+q(x)C)

-/

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

lemma polytime_fun.foldl_step {f : ptree → ptree → ptree} (hf : polytime_fun₂ f) :
  polytime_fun (foldl_step f) :=
by { apply polytime_fun.pair, apply polytime_fun.comp, apply polytime_fun.tail, apply polytime_fun.prod_fst, apply polytime_fun.comp₂ hf, apply polytime_fun.prod_snd,  apply polytime_fun.comp, apply polytime_fun.head, apply polytime_fun.prod_fst, }

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

lemma polytime_fun.foldl_fix_fun {f : ptree → ptree → ptree} (hf : polytime_fun₂ f) : polytime_fun (foldl_fix_fun f) :=
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

lemma polytime_fun.foldl {f : ptree → ptree → ptree} (hf : polytime_fun₂ f) :
  

#check list.drop

lemma fix_bounded_terminates_of_invariant {α β : Type*} (f : α → β ⊕ α) {invariant : α → Prop} [decidable_pred invariant]
  (hinv : ∀ x y, invariant x → f x = sum.inr y → invariant y) {start : α} (hstart : invariant start)
  {n : ℕ} (hn : fix_bounded_terminates f (λ _, true) n start) :
  fix_bounded_terminates f invariant n start :=
begin
  induction n with n ih generalizing start, { contradiction, },
  simp only [fix_bounded_terminates_iff] at ⊢ hn,
  refine ⟨hstart, _⟩, intros x' hx',
  apply ih, { apply hinv _ _ hstart hx', }, exact hn.2 _ hx',
end

lemma fix_bounded_while_of_terminates {α β : Type*} {f : α → β ⊕ α} {P : α → Prop} [decidable_pred P]
  {n : ℕ} {start : α} (h : fix_bounded_terminates f P n start) :
  ∃ (x : α) (y : β), y ∈ fix_bounded_while f P n start ∧ sum.inl y = f x ∧ P x :=
begin
  induction n with n ih generalizing start, { contradiction, },
  rw fix_bounded_terminates_iff at h,
  cases H : f start with val,
  { refine ⟨start, val, _, H.symm, h.1⟩,
    simp [h.1, fix_bounded_while, H], },
  simpa [h.1, fix_bounded_while, H] using ih (h.2 _ H),
end


end list
