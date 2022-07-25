import polyfix
import polysize
import data.list.basic


section foldl_lemmas

variables {α β γ : Type*} [inhabited γ]
open part_eval (with_time eval)

def foldl_step (f : α → γ → α) (x : list γ × α) : option (list γ × α) :=
if x.1.empty then none else some (x.1.tail, f x.2 x.1.head)

theorem foldl_step_eval (f : α → γ → α) (x : list γ × α) (t : ℕ) :
  eval (with_time (foldl_step f : list γ × α →. option (list γ × α)) (pfun.pure 1)) (t, x) =
  part.some (t + x.1.length, [], x.1.foldl f x.2) :=
begin
  rcases x with ⟨l, acc⟩, rw [part.eq_some_iff, part_eval.mem_eval],
  split, swap, { simp [with_time, foldl_step, pfun.pure], },
  induction l with hd tl ih generalizing acc t, { simp, },
  have : some (t + 1, tl, f acc hd) ∈ with_time (foldl_step f : list γ × α →. option (list γ × α)) (pfun.pure 1) (t, hd :: tl, acc),
  { simp [with_time, foldl_step, pfun.pure], },
  refine (part_eval.reaches_fwd this).trans _, simp at ⊢ ih, specialize ih (f acc hd) (t + 1),
  rw (show (t + (tl.length + 1) = t + 1 + tl.length), by ac_refl), exact ih,
end

theorem foldl_step_eval' (f : α → γ → α) (x : list γ × α) :
  ([], x.1.foldl f x.2) ∈ eval (foldl_step f : list γ × α →. option (list γ × α)) x :=
begin
  have : part_eval.frespects (with_time (foldl_step f : list γ × α →. option (list γ × α)) (pfun.pure 1)) (foldl_step f : list γ × α →. option (list γ × α)) _ :=
  part_eval.with_time_respects (by simp [pfun.pure]),
  have R := foldl_step_eval f x 0, simp [part.eq_some_iff] at R,
  exact this.of_eval R,
end

def foldl_inv (f : α → γ → α) (x₀ : list γ × α) : set (list γ × α) :=
{s | ∃ i ≤ x₀.1.length, s.1 = x₀.1.drop i ∧ s.2 = (x₀.1.take i).foldl f x₀.2}

theorem foldl_step_invariant (f : α → γ → α) (x₀) ⦃x y : list γ × α⦄ (hx : x ∈ foldl_inv f x₀) (hy : some y = foldl_step f x) :
  y ∈ foldl_inv f x₀ :=
begin 
  rcases x with ⟨x₁, x₂⟩, rcases x₀ with ⟨l₀, acc₀⟩,
  simp [foldl_inv] at hx ⊢,
  rcases hx with ⟨i, H, rfl, rfl⟩,
  by_cases l₀.length ≤ i,
  { simp [h, foldl_step] at hy, contradiction, },
  simp [foldl_step, list.empty_iff_eq_nil, list.drop_eq_nil_iff_le, h] at hy,
  refine ⟨i+1, _, _, _⟩,
  { rwa [nat.succ_le_iff, lt_iff_not_le], },
  { rw hy, simp [← list.drop_one], congr' 1, ac_refl, },
  rw hy, 
  suffices : l₀.take (i+1) = l₀.take i ++ [(l₀.drop i).head], { simp [this], }, 
  rw not_le at h,
  rw [list.drop_eq_nth_le_cons h, list.take_succ, list.nth_le_nth h], simp [option.to_list],
end

theorem foldl_step_eval_inv (f : α → γ → α) (x : list γ × α) :
  x.1.length + 1 ∈ part_eval.time_iter (pfun.res (foldl_step f) (foldl_inv f x)) (pfun.pure 1) x :=
begin
  rw [← pfun.coe_res_inter, ← part_eval.time_iter_invariant],
  { simp [part_eval.time_iter, pfun.pure, add_comm x.fst.length 1],
    use [[], x.1.foldl f x.2], rw ← part.eq_some_iff, convert foldl_step_eval f x 0, simp, },
  { simpa using foldl_step_invariant f x, },
  use 0, simp,
end

lemma foldl_cons_eq_reverse {δ : Type*} (l : list δ) (xs : list δ) : 
  list.foldl (λ a b, b :: a) xs l = l.reverse ++ xs :=
by { induction l with hd tl ih generalizing xs, { simp, }, simp [ih], }

lemma foldr_eq_map {δ ε} (l : list δ) (f : δ → ε) (xs : list ε) : l.foldr (λ a b, f a :: b) xs = (l.map f) ++ xs :=
by { induction l, { simp, }, simpa, }

end foldl_lemmas

section list
variables {α β γ : Type*} [polycodable α] [polycodable β] [polycodable γ]
open polycodable (encode decode)

variable (H_enc : polytime_fun (λ l : ptree, ptree.equiv_list.symm $ l.equiv_list.map (encode ∘ (@decode γ _))))

def inh : inhabited γ := ⟨decode ptree.nil⟩ 
local attribute [instance] inh

include H_enc
-- List encoding aux; used very frequently, so better have a short name
def lea : polycodable (list γ) :=
{ encode := λ l, ptree.equiv_list.symm (l.map encode),
  decode := λ v, v.equiv_list.map decode,
  decode_encode := λ _, by simp,
  polytime_decode := by { rw polytime_fun_iff', simpa using H_enc, } }

lemma lea_encode (x : list γ) : by haveI := lea H_enc; exact encode x = ptree.equiv_list.symm (x.map encode) := rfl
lemma lea_decode (x : ptree) : by haveI := lea H_enc; exact (decode x : list γ) = x.equiv_list.map decode := rfl


open part_eval (with_time eval)

lemma polytime_fun.head : by haveI := lea H_enc; exact polytime_fun (@list.head γ _) :=
by { rw polytime_fun_iff'', use [code.left, polytime_left], intro x, cases x; simp [lea_encode], refl, }

lemma polytime_fun.tail : by haveI := lea H_enc; exact polytime_fun (@list.tail γ) :=
⟨code.right, polytime_right,
by { intro x, cases x; simp [lea_decode, lea_encode], }⟩

lemma polytime_fun.cons : by haveI := lea H_enc; exact polytime_fun₂ (@list.cons γ) :=
⟨code.id, polytime_id,
by { intro x, dunfold polycodable.encode, cases x; simp [lea_encode], }⟩

lemma polytime_fun.is_empty : by haveI := lea H_enc; exact polytime_fun (@list.empty γ) :=
by { letI := lea H_enc, classical, convert_to polytime_fun (λ l : list γ, (l = [] : bool)), { ext x, cases x; simp, }, apply polytime_fun.eq_const polytime_fun.id, }

lemma polytime_fun.foldl_step {f : β → α → γ → α} (hf : polytime_fun₃ f) :
  (by haveI := lea H_enc; exact (polytime_fun₂ (λ d, foldl_step (f d)))) :=
by { letI := lea H_enc, apply polytime_fun.ite, simp, apply polytime_fun.comp, apply polytime_fun.is_empty, apply polytime_fun.comp polytime_fun.fst polytime_fun.snd, apply polytime_fun.const, apply polytime_fun.comp, apply polytime_fun.some, apply polytime_fun.pair, apply polytime_fun.comp, apply polytime_fun.tail, apply polytime_fun.comp, apply polytime_fun.fst, apply polytime_fun.snd, apply polytime_fun.comp₃ hf, apply polytime_fun.fst, apply polytime_fun.comp, apply polytime_fun.snd, apply polytime_fun.snd, apply polytime_fun.comp, apply polytime_fun.head, apply polytime_fun.comp, apply polytime_fun.fst, apply polytime_fun.snd, }

section encode_sizeof

@[simp] lemma encode_sizeof_nil : by haveI := lea H_enc; exact (encode ([] : list γ)).sizeof = 1 :=
by simp [lea_encode]
@[simp] lemma encode_sizeof_cons (a : γ) (b : list γ) :
  by haveI := lea H_enc; exact (encode (a :: b)).sizeof = 1 + (encode a).sizeof + (encode b).sizeof :=
by simp [lea_encode]

lemma encode_sizeof_le_of_mem {l : list γ} {x : γ} (hx : x ∈ l) :
  by haveI := lea H_enc; exact (encode x).sizeof ≤ (encode l).sizeof :=
begin
  induction l with hd tl ih, { simp at hx, contradiction, },
  rcases ((list.mem_cons_iff _ _ _).mp hx) with rfl|h; simp,
  { linarith only, },
  linarith only [ih h],
end

@[simp] lemma encode_sizeof_append (a b : list γ) : by haveI := lea H_enc; exact
  ((encode (a ++ b)).sizeof : ℤ) = ((encode a).sizeof : ℤ) + (encode b).sizeof - 1 :=
by { induction a with hd tl ih, { simp, }, simp [ih], ring, }

lemma encode_sizeof_le_of_infix {a b : list γ} (h : a <:+: b) : by haveI := lea H_enc; exact
  (encode a).sizeof ≤ (encode b).sizeof :=
begin
  letI := lea H_enc, rcases h with ⟨s, t, rfl⟩,
  have i₁ := one_le_encode_sizeof s, have i₂ := one_le_encode_sizeof t,
  zify at *, simp, linarith,
end

lemma encode_list_sizeof (l : list γ) : by haveI := lea H_enc; exact 
  (encode l).sizeof = (l.map (λ x, (encode x).sizeof)).sum + l.length + 1 :=
by { induction l with hd tl ih, { simp, }, simp [ih], ac_refl, }

@[simp] lemma encode_sizeof_reverse (l : list γ) : by haveI := lea H_enc; exact
  (encode l.reverse).sizeof = (encode l).sizeof :=
by { simp [encode_list_sizeof, list.sum_reverse], }

lemma len_le_encode_sizeof (a : list γ) : by haveI := lea H_enc; exact
  a.length + 1 ≤ (encode a).sizeof :=
by { induction a with hd tl ih, { simp, }, simp, linarith, }

lemma polysize_fun_map_polysize {f : β → γ → γ} (hf : polysize_fun₂ f) : by haveI := lea H_enc; exact
  polysize_fun₂ (λ (s : β) (l : list γ), l.map (f s)) :=
begin
  letI := lea H_enc,
  rcases hf with ⟨p, hp⟩,
  use (polynomial.monomial 1 1) * p + (polynomial.monomial 1 1) + 1, rintro ⟨s, l⟩, dsimp only,
  conv_lhs { rw encode_list_sizeof, },
  simp, mono,
  { refine (list.sum_le_card_nsmul (l.map (λ x, (encode (f s x)).sizeof)) (p.eval $ (encode s).sizeof + (encode l).sizeof + 1) _).trans _, 
    { intros x hx, simp at hx, rcases hx with ⟨x, hx, rfl⟩, refine (hp ⟨s, x⟩).trans _,
      apply monotone_polynomial_nat, simpa using encode_sizeof_le_of_mem H_enc hx, },
    simp, apply mul_le_mul_right', refine (nat.le_succ _).trans ((len_le_encode_sizeof H_enc l).trans _), linarith only, },
  refine (nat.le_succ _).trans ((len_le_encode_sizeof H_enc l).trans _), linarith only,
end

end encode_sizeof

theorem polytime_fun.foldl_aux {f : β → α → γ → α} {l : β → list γ} {acc : β → α} 
  (hf : polytime_fun₃ f) (hl : by haveI := lea H_enc; exact polytime_fun l) (hacc : polytime_fun acc) 
  (hs : by haveI := lea H_enc; exact polysize_fun₃ (λ (s : β) (x : α) (l : list γ), l.foldl (f s) x)) :
  polytime_fun (λ s, (l s).foldl (f s) (acc s)) :=
begin
  letI := lea H_enc,
  suffices : polytime_fun₃ (λ s (L : list γ) (a : α), (@list.nil γ, L.foldl (f s) a)),
  { have pf : polytime_fun (λ s, (s, l s, acc s)) := polytime_fun.pair polytime_fun.id (polytime_fun.pair hl hacc),
    exact polytime_fun.comp polytime_fun.snd (polytime_fun.comp this pf), },
  cases hs with ps hps,
  refine polytime_fun.eval (λ s : β, foldl_step (f s)) (λ (s : β) (x : list γ × α), ([], x.1.foldl (f s) x.2))
    _ (polynomial.monomial 1 1) (ps + polynomial.monomial 1 1) _ _,
  { exact polytime_fun.foldl_step H_enc hf, },
  { rintros s ⟨l₀, a₀⟩, simp, apply foldl_step_eval', },
  rintros S ⟨l₀, a₀⟩, use l₀.length + 1, split,
  { simp, linarith only [len_le_encode_sizeof H_enc l₀], },
  apply part_eval.time_iter_mono _ (foldl_step_eval_inv (f S) (l₀, a₀)),
  rintros ⟨l₁, a₁⟩ y, simp [pfun.mem_res], rintros h₁ h₂, refine ⟨_, h₂⟩,
  simp [foldl_inv] at h₁, rcases h₁ with ⟨i, hi, rfl, rfl⟩,
  ring_nf, simp, mono,
  { apply encode_sizeof_le_of_infix, exact (l₀.drop_suffix i).is_infix, },
  apply le_add_left, simp,
  specialize hps ⟨S, a₀, l₀.take i⟩, simp at hps, refine hps.trans (monotone_polynomial_nat _ _),
  ring_nf, simp, exact encode_sizeof_le_of_infix H_enc (l₀.take_prefix i).is_infix,
end

theorem polytime_fun.reverse_aux : by haveI := lea H_enc; exact
  polytime_fun (@list.reverse γ) :=
begin
  letI := lea H_enc,
  convert_to polytime_fun (λ l : list γ, l.foldl (λ acc hd, hd :: acc) []),
  { ext l : 1, simp [foldl_cons_eq_reverse], },
  apply polytime_fun.foldl_aux,
  { simp only [polytime_fun₃], apply polytime_fun.comp₂ (polytime_fun.cons H_enc), apply polytime_fun.comp polytime_fun.snd polytime_fun.snd, apply polytime_fun.comp polytime_fun.fst polytime_fun.snd, },
  { exact polytime_fun.id, }, { exact polytime_fun.const _, },
  simp [foldl_cons_eq_reverse], use polynomial.monomial 1 1,
  rintro ⟨a, b, c⟩, zify, simp, linarith only,
end

theorem polytime_fun.foldr_aux {f : β → γ → α → α} {l : β → list γ} {acc : β → α} 
  (hf : polytime_fun₃ f) (hl : by haveI := lea H_enc; exact polytime_fun l) (hacc : polytime_fun acc) 
  (hs : by haveI := lea H_enc; exact polysize_fun₃ (λ (s : β) (x : α) (l : list γ), l.foldr (f s) x)) :
  polytime_fun (λ s, (l s).foldr (f s) (acc s)) :=
begin
  letI := lea H_enc,
  simp only [← list.foldl_reverse], apply polytime_fun.foldl_aux,
  { apply polytime_fun.comp₃ hf polytime_fun.fst; apply polytime_fun.comp, any_goals { exact polytime_fun.snd, }, exact polytime_fun.fst, },
  { apply polytime_fun.comp (polytime_fun.reverse_aux H_enc) hl, },
  { exact hacc, },
  simp only [← list.foldr_reverse],
  suffices : polysize_fun (λ xls : β × α × list γ, (xls.1, xls.2.1, xls.2.2.reverse)),
  { exact polysize_fun.comp hs this, }, apply polysize_of_polytime_fun,
  apply polytime_fun.pair polytime_fun.fst, apply polytime_fun.pair; apply polytime_fun.comp,
  exacts [polytime_fun.fst, polytime_fun.snd, (polytime_fun.reverse_aux H_enc), polytime_fun.comp polytime_fun.snd polytime_fun.snd],
end


lemma polysize_fun.append : by haveI := lea H_enc; exact
  polysize_fun₂ (@list.append γ) :=
⟨polynomial.monomial 1 1,
by { rintro ⟨a, b⟩, zify, simp [list.append_eq_has_append], linarith, }⟩

theorem polytime_fun.map_aux {f : β → γ → γ} {l : β → list γ}
  (hf : polytime_fun₂ f)
  (hl : by haveI := lea H_enc; exact polytime_fun l) : by haveI := lea H_enc; exact
  polytime_fun (λ s, (l s).map (f s)) :=
begin
  letI := lea H_enc,
  convert_to polytime_fun (λ s : β, (l s).foldr (λ a b, f s a :: b) []),
  { ext s : 1, simp [foldr_eq_map], },
  apply polytime_fun.foldr_aux,
  { apply polytime_fun.comp₂ (polytime_fun.cons H_enc), apply polytime_fun.comp₂ hf, exact polytime_fun.fst, all_goals { apply polytime_fun.comp, }, any_goals { apply polytime_fun.snd, }, apply polytime_fun.fst, },
  { exact hl, }, { apply polytime_fun.const, },
  simp only [foldr_eq_map],
  apply polysize_fun.comp₂ (polysize_fun.append H_enc),
  { refine polysize_fun.comp (polysize_fun_map_polysize H_enc (polysize₂_of_polytime₂ hf)) (_ : polysize_fun (λ s : β × list γ × list γ, (s.1, s.2.2))), 
    apply polysize_of_polytime_fun, apply polytime_fun.pair polytime_fun.fst, apply polytime_fun.comp polytime_fun.snd polytime_fun.snd, },
  apply polysize_of_polytime_fun, apply polytime_fun.comp polytime_fun.fst polytime_fun.snd,
end

end list
