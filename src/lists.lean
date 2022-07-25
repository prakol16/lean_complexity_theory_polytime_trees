import polyfix
import data.list.basic


section list

def ptree_list_encoding_aux : polycodable (list ptree) :=
{ encode := ptree.equiv_list.symm,
  decode := ptree.equiv_list,
  decode_encode := λ _, by simp,
  polytime_decode := ⟨code.id, polytime_id, by simp⟩}

local attribute [instance] ptree_list_encoding_aux

open polycodable (encode decode)
open part_eval (with_time eval)

lemma polytime_fun.head : polytime_fun (@list.head ptree _) :=
⟨code.left, polytime_left,
by { intro x, cases x; simp [encode], refl, }⟩

lemma polytime_fun.tail : polytime_fun (@list.tail ptree) :=
⟨code.right, polytime_right,
by { intro x, cases x; simp [encode], }⟩

lemma polytime_fun.cons : polytime_fun₂ (@list.cons ptree) :=
⟨code.id, polytime_id,
by { intro x, dunfold polycodable.encode, cases x; simp [encode], }⟩

variables {α β γ : Type*} [polycodable α] [polycodable β] [polycodable γ]
def foldl_step (f : α → ptree → α) (x : list ptree × α) : option (list ptree × α) :=
if x.1 = [] then none else some (x.1.tail, f x.2 x.1.head)

lemma polytime_fun.foldl_step {f : β → α → ptree → α} (hf : polytime_fun₃ f) :
  polytime_fun₂ (λ d, foldl_step (f d)) :=
by { apply polytime_fun.ite, apply polytime_fun.eq_const, apply polytime_fun.comp polytime_fun.fst polytime_fun.snd, apply polytime_fun.const, apply polytime_fun.comp, apply polytime_fun.some, apply polytime_fun.pair, apply polytime_fun.comp, apply polytime_fun.tail, apply polytime_fun.comp, apply polytime_fun.fst, apply polytime_fun.snd, apply polytime_fun.comp₃ hf, apply polytime_fun.fst, apply polytime_fun.comp, apply polytime_fun.snd, apply polytime_fun.snd, apply polytime_fun.comp, apply polytime_fun.head, apply polytime_fun.comp, apply polytime_fun.fst, apply polytime_fun.snd, }

theorem foldl_step_eval (f : α → ptree → α) (x : list ptree × α) (t : ℕ) :
  eval (with_time (foldl_step f : list ptree × α →. option (list ptree × α)) (pfun.pure 1)) (t, x) =
  part.some (t + x.1.length, [], x.1.foldl f x.2) :=
begin
  rcases x with ⟨l, acc⟩, rw [part.eq_some_iff, part_eval.mem_eval],
  split, swap, { simp [with_time, foldl_step, pfun.pure], },
  induction l with hd tl ih generalizing acc t, { simp, },
  have : some (t + 1, tl, f acc hd) ∈ with_time (foldl_step f : list ptree × α →. option (list ptree × α)) (pfun.pure 1) (t, hd :: tl, acc),
  { simp [with_time, foldl_step, pfun.pure], },
  refine (part_eval.reaches_fwd this).trans _, simp at ⊢ ih, specialize ih (f acc hd) (t + 1),
  rw (show (t + (tl.length + 1) = t + 1 + tl.length), by ac_refl), exact ih,
end

theorem foldl_step_eval' (f : α → ptree → α) (x : list ptree × α) :
  ([], x.1.foldl f x.2) ∈ eval (foldl_step f : list ptree × α →. option (list ptree × α)) x :=
begin
  have : part_eval.frespects (with_time (foldl_step f : list ptree × α →. option (list ptree × α)) (pfun.pure 1)) (foldl_step f : list ptree × α →. option (list ptree × α)) _ :=
  part_eval.with_time_respects (by simp [pfun.pure]),
  have R := foldl_step_eval f x 0, simp [part.eq_some_iff] at R,
  exact this.of_eval R,
end

def foldl_inv (f : α → ptree → α) (x₀ : list ptree × α) : set (list ptree × α) :=
{s | ∃ i ≤ x₀.1.length, s.1 = x₀.1.drop i ∧ s.2 = (x₀.1.take i).foldl f x₀.2}

theorem foldl_step_invariant (f : α → ptree → α) (x₀) ⦃x y : list ptree × α⦄ (hx : x ∈ foldl_inv f x₀) (hy : some y = foldl_step f x) :
  y ∈ foldl_inv f x₀ :=
begin 
  rcases x with ⟨x₁, x₂⟩, rcases x₀ with ⟨l₀, acc₀⟩,
  simp [foldl_inv] at hx ⊢,
  rcases hx with ⟨i, H, rfl, rfl⟩,
  by_cases l₀.length ≤ i,
  { simp [h, foldl_step] at hy, contradiction, },
  simp [foldl_step, list.drop_eq_nil_iff_le, h] at hy,
  refine ⟨i+1, _, _, _⟩,
  { rwa [nat.succ_le_iff, lt_iff_not_le], },
  { rw hy, simp [← list.drop_one], congr' 1, ac_refl, },
  rw hy, 
  suffices : l₀.take (i+1) = l₀.take i ++ [(l₀.drop i).head], { simp [this], }, 
  rw not_le at h,
  rw [list.drop_eq_nth_le_cons h, list.take_succ, list.nth_le_nth h], simp [option.to_list],
end

theorem foldl_step_eval_inv (f : α → ptree → α) (x : list ptree × α) :
  x.1.length + 1 ∈ part_eval.time_iter (pfun.res (foldl_step f) (foldl_inv f x)) (pfun.pure 1) x :=
begin
  rw [← pfun.coe_res_inter, ← part_eval.time_iter_invariant],
  { simp [part_eval.time_iter, pfun.pure, add_comm x.fst.length 1],
    use [[], x.1.foldl f x.2], rw ← part.eq_some_iff, convert foldl_step_eval f x 0, simp, },
  { simpa using foldl_step_invariant f x, },
  use 0, simp,
end

section encode_sizeof


open polycodable (encode)

@[simp] lemma encode_sizeof_ptree (x : ptree) : (encode x).sizeof = x.sizeof := rfl
@[simp] lemma encode_sizeof_nil : (encode ([] : list ptree)).sizeof = 1 :=
by simp [encode]
@[simp] lemma encode_sizeof_cons (a : ptree) (b : list ptree) :
  (encode (a :: b)).sizeof = 1 + (encode a).sizeof + (encode b).sizeof :=
by simp [encode]
lemma one_le_encode_sizeof (x : α) :
  1 ≤ (encode x).sizeof :=
by { cases (encode x); simp, linarith only, }

lemma encode_sizeof_le_of_mem {l : list ptree} {x : ptree} (hx : x ∈ l) :
  x.sizeof ≤ (encode l).sizeof :=
begin
  induction l with hd tl ih, { simp at hx, contradiction, },
  rcases ((list.mem_cons_iff _ _ _).mp hx) with rfl|h; simp,
  { linarith only, },
  linarith only [ih h],
end

@[simp] lemma encode_sizeof_pair (a : α) (b : β) : (encode (a, b)).sizeof = (encode a).sizeof + (encode b).sizeof + 1 :=
by { simp [encode], ac_refl, }

@[simp] lemma encode_sizeof_append (a b : list ptree) :
  ((encode (a ++ b)).sizeof : ℤ) = ((encode a).sizeof : ℤ) + (encode b).sizeof - 1 :=
by { induction a with hd tl ih, { simp, }, simp [ih], ring, }

lemma encode_sizeof_le_of_infix {a b : list ptree} (h : a <:+: b) :
  (encode a).sizeof ≤ (encode b).sizeof :=
begin
  rcases h with ⟨s, t, rfl⟩,
  have i₁ := one_le_encode_sizeof s, have i₂ := one_le_encode_sizeof t,
  zify at *, simp, linarith,
end

lemma encode_list_sizeof (l : list ptree) : (encode l).sizeof = (l.map ptree.sizeof).sum + l.length + 1 :=
by { induction l with hd tl ih, { simp, }, simp [ih], ac_refl, }

@[simp] lemma encode_sizeof_reverse (l : list ptree) :
  (encode l.reverse).sizeof = (encode l).sizeof :=
by { simp [encode_list_sizeof, list.sum_reverse], }

lemma len_le_encode_sizeof (a : list ptree) :
  a.length + 1 ≤ (encode a).sizeof :=
by { induction a with hd tl ih, { simp, }, simp, linarith, }


def polysize_fun (f : α → β) : Prop :=
∃ p : polynomial ℕ, ∀ (x : α), (encode (f x)).sizeof ≤ p.eval (encode x).sizeof

lemma polysize_of_polytime_fun {f : α → β} (hf : polytime_fun f) :
  polysize_fun f :=
begin
  rcases hf with ⟨c, ⟨p, hp⟩, sc⟩, use p,
  intro x, specialize sc x, rw part.eq_some_iff at sc,
  rcases hp (encode x) with ⟨t, ht, t_le⟩,
  exact (eval_sizeof_le_time sc ht).trans t_le,
end

lemma polysize_fun.comp {g : β → γ} {f : α → β} (hg : polysize_fun g) (hf : polysize_fun f) :
  polysize_fun (g ∘ f) :=
begin
  rcases hf with ⟨pf, hpf⟩, rcases hg with ⟨pg, hpg⟩,
  use pg.comp pf, intro x, simp,
  refine (hpg _).trans (monotone_polynomial_nat _ _),
  apply hpf,
end

section
variables {δ ε : Type*} [polycodable δ] [polycodable ε]

def polysize_fun₂ (f : α → β → γ) : Prop := polysize_fun (function.uncurry f)
lemma polysize₂_of_polytime₂ {f : α → β → γ} (hf : polytime_fun₂ f) : polysize_fun₂ f :=
polysize_of_polytime_fun hf

lemma polysize_fun.pair {f : α → β} {g : α → γ} (hf : polysize_fun f) (hg : polysize_fun g) :
  polysize_fun (λ s, (f s, g s)) :=
by { cases hf with pf hpf, cases hg with pg hpg, use pf + pg + 1, intro x, simpa using add_le_add (hpf _) (hpg _), }

lemma polysize_fun.comp₂ {f : α → β → γ} {g : δ → α} {h : δ → β} (hf : polysize_fun₂ f) (hg : polysize_fun g) (hh : polysize_fun h) :
  polysize_fun (λ s, f (g s) (h s)) :=
polysize_fun.comp hf (polysize_fun.pair hg hh)


def polysize_fun₃ (f : α → β → γ → δ) : Prop :=
polysize_fun (λ a : α × β × γ, f a.1 a.2.1 a.2.2)
lemma polysize₃_of_polytime₃ {f : α → β → γ → δ} (hf : polytime_fun₃ f) : polysize_fun₃ f :=
polysize_of_polytime_fun hf
lemma polysize_fun.comp₃ {f : α → β → γ → δ} {g : ε → α} {h : ε → β} {i : ε → γ}
  (hf : polysize_fun₃ f) (hg : polysize_fun g) (hh : polysize_fun h) (hi : polysize_fun i) :
  polysize_fun (λ s, f (g s) (h s) (i s)) :=
polysize_fun.comp hf (polysize_fun.pair hg (polysize_fun.pair hh hi))

end

lemma polysize_fun_map_polysize {f : β → ptree → ptree} (hf : polysize_fun₂ f) :
  polysize_fun₂ (λ (s : β) (l : list ptree), l.map (f s)) :=
begin
  rcases hf with ⟨p, hp⟩,
  use (polynomial.monomial 1 1) * p + (polynomial.monomial 1 1) + 1, rintro ⟨s, l⟩, dsimp only,
  conv_lhs { rw encode_list_sizeof, },
  simp, mono,
  { refine (list.sum_le_card_nsmul (l.map (ptree.sizeof ∘ f s)) (p.eval $ (encode s).sizeof + (encode l).sizeof + 1) _).trans _, 
    { intros x hx, simp at hx, rcases hx with ⟨x, hx, rfl⟩, refine (hp ⟨s, x⟩).trans _,
      apply monotone_polynomial_nat, simpa using encode_sizeof_le_of_mem hx, },
    simp, apply mul_le_mul_right', refine (nat.le_succ _).trans ((len_le_encode_sizeof l).trans _), linarith only, },
  refine (nat.le_succ _).trans ((len_le_encode_sizeof l).trans _), linarith only,
end

end encode_sizeof

theorem polytime_fun.foldl_aux {f : β → α → ptree → α} {l : β → list ptree} {acc : β → α} 
  (hf : polytime_fun₃ f) (hl : polytime_fun l) (hacc : polytime_fun acc) 
  (hs : polysize_fun₃ (λ (s : β) (x : α) (l : list ptree), l.foldl (f s) x)) :
  polytime_fun (λ s, (l s).foldl (f s) (acc s)) :=
begin
  suffices : polytime_fun₃ (λ s (L : list ptree) (a : α), (@list.nil ptree, L.foldl (f s) a)),
  { have pf : polytime_fun (λ s, (s, l s, acc s)) := polytime_fun.pair polytime_fun.id (polytime_fun.pair hl hacc),
    exact polytime_fun.comp polytime_fun.snd (polytime_fun.comp this pf), },
  cases hs with ps hps,
  refine polytime_fun.eval (λ s : β, foldl_step (f s)) (λ (s : β) (x : list ptree × α), ([], x.1.foldl (f s) x.2))
    _ (polynomial.monomial 1 1) (ps + polynomial.monomial 1 1) _ _,
  { exact polytime_fun.foldl_step hf, },
  { rintros s ⟨l₀, a₀⟩, simp, apply foldl_step_eval', },
  rintros S ⟨l₀, a₀⟩, use l₀.length + 1, split,
  { simp, linarith only [len_le_encode_sizeof l₀], },
  apply part_eval.time_iter_mono _ (foldl_step_eval_inv (f S) (l₀, a₀)),
  rintros ⟨l₁, a₁⟩ y, simp [pfun.mem_res], rintros h₁ h₂, refine ⟨_, h₂⟩,
  simp [foldl_inv] at h₁, rcases h₁ with ⟨i, hi, rfl, rfl⟩,
  ring_nf, simp, mono,
  { apply encode_sizeof_le_of_infix, exact (l₀.drop_suffix i).is_infix, },
  apply le_add_left, simp,
  specialize hps ⟨S, a₀, l₀.take i⟩, simp at hps, refine hps.trans (monotone_polynomial_nat _ _),
  ring_nf, simp, exact encode_sizeof_le_of_infix (l₀.take_prefix i).is_infix,
end

lemma foldl_cons_eq_reverse {δ : Type*} (l : list δ) (xs : list δ) : 
  list.foldl (λ a b, b :: a) xs l = l.reverse ++ xs :=
by { induction l with hd tl ih generalizing xs, { simp, }, simp [ih], }

theorem polytime_fun.reverse_aux : polytime_fun (@list.reverse ptree) :=
begin
  convert_to polytime_fun (λ l : list ptree, l.foldl (λ acc hd, hd :: acc) []),
  { ext l : 1, simp [foldl_cons_eq_reverse], },
  apply polytime_fun.foldl_aux,
  { simp only [polytime_fun₃], apply polytime_fun.comp₂ polytime_fun.cons, apply polytime_fun.comp polytime_fun.snd polytime_fun.snd, apply polytime_fun.comp polytime_fun.fst polytime_fun.snd, },
  { exact polytime_fun.id, }, { exact polytime_fun.const _, },
  simp [foldl_cons_eq_reverse], use polynomial.monomial 1 1,
  rintro ⟨a, b, c⟩, zify, simp, linarith only,
end

theorem polytime_fun.foldr_aux {f : β → ptree → α → α} {l : β → list ptree} {acc : β → α} 
  (hf : polytime_fun₃ f) (hl : polytime_fun l) (hacc : polytime_fun acc) 
  (hs : polysize_fun₃ (λ (s : β) (x : α) (l : list ptree), l.foldr (f s) x)) :
  polytime_fun (λ s, (l s).foldr (f s) (acc s)) :=
begin
  simp only [← list.foldl_reverse], apply polytime_fun.foldl_aux,
  { apply polytime_fun.comp₃ hf polytime_fun.fst; apply polytime_fun.comp, any_goals { exact polytime_fun.snd, }, exact polytime_fun.fst, },
  { apply polytime_fun.comp polytime_fun.reverse_aux hl, },
  { exact hacc, },
  simp only [← list.foldr_reverse],
  suffices : polysize_fun (λ xls : β × α × list ptree, (xls.1, xls.2.1, xls.2.2.reverse)),
  { exact polysize_fun.comp hs this, }, apply polysize_of_polytime_fun,
  apply polytime_fun.pair polytime_fun.fst, apply polytime_fun.pair; apply polytime_fun.comp,
  exacts [polytime_fun.fst, polytime_fun.snd, polytime_fun.reverse_aux, polytime_fun.comp polytime_fun.snd polytime_fun.snd],
end

lemma foldr_eq_map {δ ε} (l : list δ) (f : δ → ε) (xs : list ε) : l.foldr (λ a b, f a :: b) xs = (l.map f) ++ xs :=
by { induction l, { simp, }, simpa, }

lemma polysize_fun.append : polysize_fun₂ (@list.append ptree) :=
⟨polynomial.monomial 1 1,
by { rintro ⟨a, b⟩, zify, simp [list.append_eq_has_append], linarith, }⟩

theorem polytime_fun.map_aux {f : β → ptree → ptree} {l : β → list ptree} (hf : polytime_fun₂ f) (hl : polytime_fun l) :
  polytime_fun (λ s, (l s).map (f s)) :=
begin
  convert_to polytime_fun (λ s : β, (l s).foldr (λ a b, f s a :: b) []),
  { ext s : 1, simp [foldr_eq_map], },
  apply polytime_fun.foldr_aux,
  { apply polytime_fun.comp₂ polytime_fun.cons, apply polytime_fun.comp₂ hf, exact polytime_fun.fst, all_goals { apply polytime_fun.comp, }, any_goals { apply polytime_fun.snd, }, apply polytime_fun.fst, },
  { exact hl, }, { apply polytime_fun.const, },
  simp only [foldr_eq_map],
  apply polysize_fun.comp₂ polysize_fun.append,
  { refine polysize_fun.comp (polysize_fun_map_polysize (polysize₂_of_polytime₂ hf)) (_ : polysize_fun (λ s : β × list ptree × list ptree, (s.1, s.2.2))), 
    apply polysize_of_polytime_fun, apply polytime_fun.pair polytime_fun.fst, apply polytime_fun.comp polytime_fun.snd polytime_fun.snd, },
  apply polysize_of_polytime_fun, apply polytime_fun.comp polytime_fun.fst polytime_fun.snd,
end

local attribute [-instance] ptree_list_encoding_aux

instance : polycodable (list α) :=
@polycodable.mk' (list ptree) ptree_list_encoding_aux (list α)
(list.map encode)
(list.map decode)
(by simp)
begin
  simp, apply polytime_fun.map_aux, swap,
  { apply polytime_fun.id, },
  simp only [polytime_fun₂, function.uncurry], apply polytime_fun.comp,
  apply polytime_fun.comp polytime_fun.encode polytime_fun.decode', apply polytime_fun.snd,
end

lemma encode_list_ptree_eq (l : list ptree) :
  encode l = ptree.equiv_list.symm l :=
by { simp [encode], }

private lemma polytime_fun_list_ptree_iff (f : α → list ptree → β) :
  polytime_fun₂ f ↔ @polytime_fun₂ _ _ _ _ ptree_list_encoding_aux _ f :=
by { simp [polytime_fun₂, polytime_fun, function.uncurry, encode], }

end list
