import polyfix
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

def foldr_step (f : ptree → ptree) (l : list ptree × list ptree) : list ptree ⊕ (list ptree × list ptree) :=
if l.1 = [] then sum.inl l.2 else sum.inr (l.1.tail, f l.1.head :: l.2)

lemma polytime_foldr_step {f : ptree → ptree} (hf : polytime_fun f) : polytime_fun (foldr_step f) :=
begin
  apply polytime_fun.ite, apply polydecidable_of_preimage_polytime (=[]), apply polytime_fun.prod_fst, apply polydecidable.eq_const,
  apply polytime_fun.comp, apply polytime_fun.sum_inl, apply polytime_fun.prod_snd, apply polytime_fun.comp,
  apply polytime_fun.sum_inr, apply polytime_fun.pair, apply polytime_fun.comp, apply polytime_fun.tail, apply polytime_fun.prod_fst,
  apply polytime_fun.comp₂, apply polytime_fun.cons, apply polytime_fun.comp hf, apply polytime_fun.comp, apply polytime_fun.head, apply polytime_fun.prod_fst, apply polytime_fun.prod_snd, 
end

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

lemma fix_bounded_while_of_terminates' {α β : Type*} {f : α → β ⊕ α} (g : β) {P : α → Prop} [decidable_pred P]
  {n : ℕ} {start : α} (h : fix_bounded_terminates f P n start) (hg : ∀ {x : α} {y : β}, P x → sum.inl y = f x → y = g) :
  g ∈ fix_bounded_while f P n start :=
by { obtain ⟨x, y, hy, hx, hinv⟩ := fix_bounded_while_of_terminates h, rwa ← hg hinv hx, }

lemma foldr_step_len {f : ptree → ptree} (hf : polytime_fun f) (l : list ptree) :
  fix_bounded_while (foldr_step f)
  (λ x, l.length = x.1.length + x.2.length ∧
        x.2 = ((l.take x.2.length).map f).reverse ∧
        x.1 = l.drop x.2.length) (l.length + 1)
  (l, []) = some (l.map f).reverse :=
begin
  apply fix_bounded_while_of_terminates', swap,
  { rintros ⟨x₁, x₂⟩ y ⟨hinv₁, hinv₂, hinv₃⟩ hy, dsimp only at hinv₁ hinv₂ hinv₃,
    simp only [foldr_step, sum_inl_eq_ite] at hy, rcases hy with ⟨rfl, rfl⟩, 
    simp at hinv₁, simpa [← hinv₁] using hinv₂, },
  apply fix_bounded_terminates_of_invariant,
  { rintros ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨hinv₁, hinv₂, hinv₃⟩ hy, dsimp only at *, rw @comm _ (=) at hy,
    simp only [foldr_step, sum_inr_eq_ite, prod.mk.inj_iff] at hy, rcases hy with ⟨hx₁, rfl, rfl⟩,
    cases x₁ with hd tl, { contradiction, }, clear hx₁,
    split, { rw hinv₁, simp, ring, },
    have x₂lt : x₂.length < l.length, { rw hinv₁, simp, },
    simp only [list.drop_eq_nth_le_cons x₂lt] at hinv₃,
    split, { simpa [list.take_succ, list.nth_le_nth x₂lt, option.to_list, ← hinv₃.1], },
    simpa using hinv₃.2, },
  { split; simp, },
  { suffices : ∀ a, fix_bounded_terminates (foldr_step f) (λ _, true) (l.length + 1) (l, a), apply this,
    induction l with hd tl ih, { intro a, simp [foldr_step], },
    intro a, rw fix_bounded_terminates_iff,
    simp [-fix_bounded_terminates_iff, foldr_step],
    rintros _ _ rfl rfl, apply ih, },
end



end list
