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

lemma polytime_fun.foldl {f : ptree → ptree → ptree → ptree} {g : ptree → list ptree} {acc : ptree → ptree}
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
      sorry, },
    sorry, },
  { apply polytime_fun.foldl_fix_fun hf, }
end


end list
