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

lemma polytime_fun.head_aux : by haveI := lea H_enc; exact polytime_fun (@list.head γ _) :=
by { rw polytime_fun_iff'', use [code.left, polytime_left], intro x, cases x; simp [lea_encode], refl, }

lemma polytime_fun.tail_aux : by haveI := lea H_enc; exact polytime_fun (@list.tail γ) :=
⟨code.right, polytime_right,
by { intro x, cases x; simp [lea_decode, lea_encode], }⟩

lemma polytime_fun.cons_aux : by haveI := lea H_enc; exact polytime_fun₂ (@list.cons γ) :=
⟨code.id, polytime_id,
by { intro x, dunfold polycodable.encode, cases x; simp [lea_encode], }⟩

lemma polytime_fun.is_empty_aux : by haveI := lea H_enc; exact polytime_fun (@list.empty γ) :=
by { letI := lea H_enc, classical, convert_to polytime_fun (λ l : list γ, (l = [] : bool)), { ext x, cases x; simp, }, polyfun, }

lemma polytime_fun.foldl_step {f : β → α → γ → α} (hf : polytime_fun₃ f) :
  (by haveI := lea H_enc; exact (polytime_fun₂ (λ d, foldl_step (f d)))) :=
begin
  letI := lea H_enc,
  have := polytime_fun.head_aux H_enc, have := polytime_fun.tail_aux H_enc, have := polytime_fun.is_empty_aux H_enc,
  delta foldl_step,
  polyfun,
end

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

lemma encode_sizeof_le_of_sublist {a b : list γ} (h : a <+ b) : by haveI := lea H_enc; exact
  (encode a).sizeof ≤ (encode b).sizeof :=
begin
  induction h, { simp, },
  case list.sublist.cons : l₁ l₂ s₁ H ih { refine ih.trans _, simp, },
  case list.sublist.cons2 : l₁ l₂ s₁ H ih { simpa, },
end

lemma encode_sizeof_le_of_infix {a b : list γ} (h : a <:+: b) : by haveI := lea H_enc; exact
  (encode a).sizeof ≤ (encode b).sizeof :=
encode_sizeof_le_of_sublist H_enc h.sublist

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
  { have pf : polytime_fun (λ s, (s, l s, acc s)) := by polyfun,
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
  { have := polytime_fun.cons_aux H_enc, polyfun, },
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
  { polyfun, },
  { apply polytime_fun.comp (polytime_fun.reverse_aux H_enc) hl, },
  { exact hacc, },
  simp only [← list.foldr_reverse],
  suffices : polysize_fun (λ xls : β × α × list γ, (xls.1, xls.2.1, xls.2.2.reverse)),
  { exact polysize_fun.comp hs this, },
  apply polysize_of_polytime_fun,
  have := polytime_fun.reverse_aux H_enc, polyfun,
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
  { have := polytime_fun.cons_aux H_enc, polyfun, },
  { exact hl, }, { apply polytime_fun.const, },
  simp only [foldr_eq_map],
  apply polysize_fun.comp₂ (polysize_fun.append H_enc),
  { refine polysize_fun.comp (polysize_fun_map_polysize H_enc (polysize₂_of_polytime₂ hf)) (_ : polysize_fun (λ s : β × list γ × list γ, (s.1, s.2.2))), 
    apply polysize_of_polytime_fun, polyfun, },
  apply polysize_of_polytime_fun, polyfun,
end

end list

section list_ptree
open polycodable (encode decode)

def list_ptree_encode : polycodable (list ptree) :=
lea ⟨code.id, polytime_id, by simp [encode, decode]⟩

local attribute [instance] list_ptree_encode

lemma H_enc {γ : Type*} [polycodable γ] : 
  polytime_fun (λ l : ptree, ptree.equiv_list.symm $ l.equiv_list.map (encode ∘ (@decode γ _))) :=
begin
  suffices : polytime_fun (λ l : list ptree, l.map (encode ∘ (@decode γ _))),
  { rcases this with ⟨c, pc, s⟩, use [c, pc], intro x, specialize s x.equiv_list, simp [encode, list_ptree_encode, lea_encode] at s, simp [s], },
  apply polytime_fun.map_aux; polyfun,
end

end list_ptree

section list
open polycodable (encode decode)

variables {α β γ : Type*} [polycodable α] [polycodable β] [polycodable γ]
instance : polycodable (list α) :=
lea H_enc

@[higher_order]
lemma polycodable.list_encode (l : list α) :
  encode l = ptree.equiv_list.symm (l.map encode) := rfl
@[higher_order]
lemma polycodable.list_decode (v : ptree) :
  @decode (list α) _ v = (ptree.equiv_list v).map decode := rfl
@[simp] lemma polycodable.list_ptree_encode :
  @encode (list ptree) _ = ptree.equiv_list.symm :=
by { ext l, rw polycodable.list_encode, simp, erw l.map_id, }
@[simp] lemma polycodable.list_ptree_decode :
  @decode (list ptree) _ = ptree.equiv_list :=
by { ext l, rw polycodable.list_decode, erw l.equiv_list.map_id, }

@[polyfun]
lemma polytime_fun.ptree_equiv_list : polytime_fun ptree.equiv_list :=
by { rw ← polycodable.list_ptree_decode, polyfun, }
@[polyfun]
lemma polytime_fun.ptree_equiv_list_symm : polytime_fun ptree.equiv_list.symm :=
by { rw ← polycodable.list_ptree_encode, polyfun, }


lemma polytime_fun.head : polytime_fun (@list.head γ ⟨decode ptree.nil⟩) :=
polytime_fun.head_aux H_enc

local attribute [polyfun] polytime_fun.head

@[polyfun]
lemma polytime_fun.tail : polytime_fun (@list.tail γ) :=
polytime_fun.tail_aux H_enc

@[polyfun]
lemma polytime_fun.cons : polytime_fun₂ (@list.cons γ) :=
polytime_fun.cons_aux H_enc

@[polyfun]
lemma polytime_fun.is_empty : polytime_fun (@list.empty γ) :=
polytime_fun.is_empty_aux H_enc

@[polyfun]
lemma polytime_fun.head' : polytime_fun (@list.head' γ) :=
begin
  convert_to polytime_fun (λ l : list γ, if l.empty then none else some (@list.head _ ⟨decode ptree.nil⟩ l)),
  { ext l : 1, cases l; simp, }, polyfun,
end

@[polyfun]
lemma polytime_fun.ihead [inhabited γ] : polytime_fun (@list.head γ _) :=
begin
  convert_to polytime_fun (λ l : list γ, l.head'.iget),
  { ext l, cases l; simp, }, polyfun,
end

local attribute [-polyfun] polytime_fun.head

@[polyfun]
theorem polytime_fun.foldr {f : β → γ → α → α} {l : β → list γ} {acc : β → α} 
  (hf : polytime_fun₃ f) (hl : polytime_fun l) (hacc : polytime_fun acc) 
  (hs : polysize_fun₃ (λ (s : β) (x : α) (l : list γ), l.foldr (f s) x)) :
  polytime_fun (λ s, (l s).foldr (f s) (acc s)) :=
polytime_fun.foldr_aux H_enc hf hl hacc hs

@[polyfun]
theorem polytime_fun.reverse : polytime_fun (@list.reverse γ) :=
polytime_fun.reverse_aux H_enc

@[polyfun]
theorem polytime_fun.foldl {f : β → α → γ → α} {l : β → list γ} {acc : β → α} 
  (hf : polytime_fun₃ f) (hl : polytime_fun l) (hacc : polytime_fun acc) 
  (hs : polysize_fun₃ (λ (s : β) (x : α) (l : list γ), l.foldl (f s) x)) :
  polytime_fun (λ s, (l s).foldl (f s) (acc s)) :=
polytime_fun.foldl_aux H_enc hf hl hacc hs

@[polyfun]
theorem polytime_fun.map {f : β → γ → α} {l : β → list γ}
  (hf : polytime_fun₂ f)
  (hl : polytime_fun l) :
  polytime_fun (λ s, (l s).map (f s)) :=
begin
  have H₁ : polytime_fun (λ l : list γ, l.map encode),
  { apply polytime_fun.decode, simp, apply polytime_fun.encode, },
  have H₂ : polytime_fun (λ (S : β × list ptree), S.2.map (encode ∘ (f S.1) ∘ decode)),
  { apply polytime_fun.map_aux H_enc; polyfun, },
  have H₃ : polytime_fun (λ l : list ptree, l.map (@decode α _)),
  { apply polytime_fun.decode, simp [polycodable.list_encode'],
    apply polytime_fun.comp polytime_fun.ptree_equiv_list_symm, simp, apply polytime_fun.map_aux H_enc; polyfun, },
  have H₁' : polytime_fun (λ (s : β), (s, (l s).map encode)), { polyfun, },
  convert H₃.comp (H₂.comp H₁'), ext, simp,
end

lemma foldr_eta' (l₁ l₂ : list α) : l₁.foldr list.cons l₂ = l₁ ++ l₂ :=
by { induction l₁ with hd tl ih, { simp, }, simpa, }

lemma len_le_encode_sizeof' (l : list α) :
  l.length ≤ (encode l).sizeof :=
by { refine (nat.le_succ _).trans _, apply len_le_encode_sizeof, }

theorem polysize_foldl (f : β → α → γ → α) (hf : ∃ p : polynomial ℕ, ∀ s acc hd, (encode (f s acc hd)).sizeof ≤ (encode acc).sizeof + p.eval (encode (s, hd)).sizeof) :
  polysize_fun₃ (λ (s : β) (x : α) (l : list γ), l.foldl (f s) x) :=
begin
  rcases hf with ⟨p, hp⟩,
  have : ∀ (s : β) (x : α) (l : list γ), (encode (l.foldl (f s) x)).sizeof ≤ (encode x).sizeof + (p.eval (encode (s, l)).sizeof) * l.length,
  { intros s x l, induction l with hd tl ih generalizing x, { simp, },
    simp, refine (ih _).trans _, rw [add_comm tl.length 1, mul_add, ← add_assoc], 
    mono*, { refine (hp _ _ _).trans _, simp, apply monotone_polynomial_nat, linarith only, },
    all_goals { simp, }, }, 
  use polynomial.monomial 1 1 + p * (polynomial.monomial 1 1),
  rintros ⟨s, x, l⟩, simp, refine (this _ _ _).trans _, mono*,
  { linarith only, }, { simp, linarith only, },
  refine (len_le_encode_sizeof' _).trans _, all_goals { linarith only, },
end

theorem polysize_foldr {f : β → γ → α → α} (hf : ∃ p : polynomial ℕ, ∀ s hd acc, (encode (f s hd acc)).sizeof ≤ (encode acc).sizeof + p.eval (encode (s, hd)).sizeof) :
  polysize_fun₃ (λ (s : β) (x : α) (l : list γ), l.foldr (f s) x) :=
begin
  simp_rw ← list.foldl_reverse, dunfold polysize_fun₃,
  refine polysize_fun.comp (_ : polysize_fun (λ sxl : β × α × list γ, sxl.2.2.foldl (λ y x, f sxl.1 x y) sxl.2.1)) (_ : polysize_fun (λ sxl : β × α × list γ, (sxl.1, sxl.2.1, sxl.2.2.reverse))),
  { skip, apply polysize_foldl (λ s acc hd, f s hd acc), dsimp, rcases hf with ⟨p, hp⟩, use p, intros, apply hp, },
  { apply polysize_of_polytime_fun, polyfun, },
end

@[polyfun]
theorem polytime_fun.append : polytime_fun₂ (@list.append γ) :=
begin
  change polytime_fun₂ (λ (l₁ l₂ : list γ), l₁ ++ l₂), simp_rw ← foldr_eta', polyfun,
  use polynomial.monomial 1 1, rintro ⟨⟨a, b⟩, c, d⟩,  simp_rw foldr_eta', zify, simp, linarith only,
end

@[polyfun]
lemma polytime_fun.append₂ : polytime_fun₂ (λ (a b : list α), a ++ b) := polytime_fun.append

section bool

@[polyfun]
lemma polytime_fun.all {f : β → α → bool} {l : β → list α} (hf : polytime_fun₂ f) (hl : polytime_fun l) :
  polytime_fun (λ s, (l s).all (f s)) :=
by { simp only [list.all], polyfun, apply polysize_fun_of_fin_range, }

@[polyfun]
lemma polytime_fun.any {f : β → α → bool} {l : β → list α} (hf : polytime_fun₂ f) (hl : polytime_fun l) :
  polytime_fun (λ s, (l s).any (f s)) :=
by { simp only [list.any], polyfun, apply polysize_fun_of_fin_range, }

end bool

@[polyfun]
lemma polytime_fun.last : polytime_fun (@list.last' α) :=
begin
  convert_to polytime_fun (λ l : list α, l.reverse.head'), { ext l : 1, induction l using list.reverse_rec_on; simp, },
  polyfun,
end

lemma polytime_fun.filter {f : β → α → bool} {l : β → list α} (hf : polytime_fun₂ f)
  (hl : polytime_fun l) : polytime_fun (λ s, (l s).filter (λ x, f s x)) :=
begin
  have filter_eq : ∀ (xs : list α) (l : list α) (P : α → bool), l.foldr (λ hd acc, if P hd then hd :: acc else acc) xs = (l.filter (λ x, P x)) ++ xs,
  { intros xs l P, induction l with hd tl ih, { simp, }, cases H : P hd; simpa [H], },
  convert_to polytime_fun (λ s : β, (l s).foldr (λ hd acc, if f s hd then hd :: acc else acc) []),
  { ext s : 1, simp [filter_eq], }, polyfun,
  apply polysize_foldr, 
  use polynomial.monomial 1 1, 
  intros s hd acc, split_ifs; simp, linarith only,
end

@[simp]
def list.izip {α β : Type*} [inhabited α] [inhabited β] : list α → list β → list (α × β)
| (x :: xs) (y :: ys) := (x, y) :: (xs.izip ys)
| [] (y :: ys) := (default, y) :: (list.izip [] ys)
| (x :: xs) [] := (x, default) :: (list.izip xs [])
| [] [] := []

def unary_nat_encode : polycodable ℕ := 
polycodable.of_equiv equiv.list_unit_equiv.symm

local attribute [instance] unary_nat_encode

lemma unary_nat_encode_eq (n : ℕ) : encode n = encode (list.repeat () n) := rfl

@[polyfun]
lemma polytime_fun.unary_length : polytime_fun (@list.length α) :=
begin
  convert_to polytime_fun (λ l : list α, equiv.list_unit_equiv (l.map (λ _, ()))),
  { ext l, simp [equiv.list_unit_equiv], }, polyfun,
end

@[polyfun]
lemma polytime_fun.unary_repeat : polytime_fun₂ (@list.repeat α) :=
begin
  convert_to polytime_fun₂ (λ (x : α) (n : ℕ), (equiv.list_unit_equiv.symm n).map (λ _, x)),
  { ext : 2, simp [equiv.list_unit_equiv], }, polyfun,
end

@[polyfun]
lemma polytime_fun.unary_nat_add : polytime_fun₂ ((+) : ℕ → ℕ → ℕ) :=
begin
  convert_to polytime_fun₂ (λ n m, (list.repeat () n ++ list.repeat () m).length),
  { ext, simp, }, polyfun,
end

@[simp] lemma encode_unit_sizeof : (encode ()).sizeof = 1 :=
by { simp [encode], }

@[simp] lemma encode_unary_nat_sizeof (n : ℕ) : (encode n).sizeof = 2 * n + 1 :=
by { simp [unary_nat_encode_eq, encode_list_sizeof], ring, }

@[polyfun]
lemma polytime_fun.unary_iterate {f : α → β → β} {n : α → ℕ} (hf : polytime_fun₂ f) (hn : polytime_fun n)
  (H : polysize_fun₃ (λ s (i : ℕ), (f s)^[i])) : polytime_fun₂ (λ s, (f s)^[n s]) :=
begin
  convert_to polytime_fun₂ (λ (s : α) (x : β), (list.repeat () (n s)).foldr (λ _, f s) x),
  { simp [list.foldr_const], },
  polyfun, change polysize_fun₃ (λ s x l, _), simp [list.foldr_const],
  refine H.comp (_ : polysize_fun (λ (sxl : (α × β) × β × list unit), (sxl.1.1, sxl.2.2.length, sxl.2.1))),
  apply polysize_of_polytime_fun, polyfun,
end

lemma _root_.nat.le_mul_right (a : ℕ) {b : ℕ} (hb : b ≠ 0) : a ≤ a * b :=
by { cases b, { contradiction, }, simp [nat.mul_succ], }


lemma polysize_fun.iterate_of_bounded_growth' {f : α → β → β} (hf : ∃ C : polynomial ℕ, ∀ a b, (encode $ f a b).sizeof ≤ (encode b).sizeof + C.eval (encode a).sizeof) :
  polysize_fun₃ (λ s (i : ℕ), (f s)^[i]) :=
begin
  rcases hf with ⟨c, hc⟩,
  have : ∀ a b (i : ℕ), (encode ((f a)^[i] b)).sizeof ≤ (encode b).sizeof + (c.eval (encode a).sizeof) * i,
  { intros a b i, induction i with i ih, { simp, }, simp [function.iterate_succ', nat.mul_succ], refine (hc _ _).trans _, rw ← add_assoc, simpa, },
  use polynomial.monomial 1 1 + c * (polynomial.monomial 1 1), rintro ⟨s, i, l⟩, simp, refine (this _ _ _).trans _,
  mono*; linarith only,
end

lemma polysize_fun.iterate_of_bounded_growth {f : α → β → β} (hf : ∃ C, ∀ a b, (encode $ f a b).sizeof ≤ (encode b).sizeof + C) :
  polysize_fun₃ (λ s (i : ℕ), (f s)^[i]) :=
by { rcases hf with ⟨c, hc⟩, apply polysize_fun.iterate_of_bounded_growth', use c, simpa, }

lemma _root_.list.range_sum (n : ℕ) : 2 * (list.range n).sum =  n * (n - 1) :=
begin
  induction n with n ih, { simp, },
  simp [list.range_succ, mul_add, ih],
  cases n; simp [nat.succ_eq_add_one], ring,
end

lemma polysize_unary_range : polysize_fun list.range :=
begin
  use (polynomial.monomial 2 1), intro x,
  simp [encode_list_sizeof],
  rw list.sum_map_mul_left, simp [list.range_sum], cases x, { simp, },
  simp [nat.succ_eq_add_one], nlinarith,
end

@[polyfun]
lemma polytime_fun.unary_range : polytime_fun list.range :=
begin
  have : ∀ (l : list unit) (xs : list ℕ), l.foldr (λ _ (acc : list ℕ), 0 :: acc.map (+1)) xs =
    (list.range l.length) ++ (xs.map (+l.length)),
  { intros l xs, induction l with hd tl ih, { simp, }, simp [list.range_succ_eq_map, ih], },
  convert_to polytime_fun (λ n, (list.repeat () n).foldr (λ _ (acc : list ℕ), 0 :: acc.map (+1)) []),
  { ext n : 1, simp [this], }, 
  polyfun, change polysize_fun₃ (λ s l xs, _), simp only [this],
  apply polysize_fun.comp₂ (polysize_fun.append _), swap, { apply polysize_of_polytime_fun, polyfun, },
  apply polysize_fun.comp polysize_unary_range, apply polysize_of_polytime_fun, polyfun,
end

@[simp] lemma _root_.list.drop_succ {α : Type*} (l : list α) (n : ℕ) :
  l.drop (n+1) = l.tail.drop n :=
by { induction l; simp, }

@[polyfun]
lemma polytime_fun.drop : polytime_fun₂ (@list.drop α) :=
begin
  convert_to polytime_fun₂ (λ n l, list.tail^[n] l),
  { ext n l : 2, induction n generalizing l; simp [*], },
  polyfun, apply polysize_fun.iterate_of_bounded_growth, use 0, intros _ b,
  cases b; simp,
end

@[polyfun]
lemma polytime_fun.nth : polytime_fun₂ (@list.nth α) :=
begin
  convert_to polytime_fun₂ (λ (l : list α) n, (l.drop n).head'),
  { ext l n : 2, simp [← list.nth_zero, list.nth_drop], },
  polyfun,
end

@[polyfun]
lemma polytime_fun.inth [inhabited α] : polytime_fun₂ (@list.inth α _) :=
by { change polytime_fun₂ (λ (l : list α) n, (l.nth n).iget), polyfun, }

@[polyfun]
lemma polytime_fun.unary_nat_tsub : polytime_fun₂ (has_sub.sub : ℕ → ℕ → ℕ) :=
begin
  convert_to polytime_fun₂ (λ m n, ((list.repeat () m).drop n).length),
  { ext m n, simp, }, polyfun,
end

@[polyfun]
lemma polytime_fun.unary_nat_le {f g : α → ℕ} (hf : polytime_fun f) (hg : polytime_fun g) :
  polytime_fun (λ n, (f n ≤ g n : bool)) :=
begin
  convert_to polytime_fun (λ n, ((f n - g n) = 0 : bool)),
  { ext n, simp, }, polyfun,
end

@[polyfun]
lemma polytime_fun.unary_nat_min : polytime_fun₂ (@min ℕ _) :=
by { change polytime_fun₂ (λ n m, if n ≤ m then n else m), polyfun, }

lemma _root_.list.nth_eq_some_nth_le {α} (l : list α) (n : ℕ) (hn : n < l.length) : l.nth n = some (l.nth_le n hn) :=
by { rw list.nth_eq_some, exact ⟨_, rfl⟩, }

@[polyfun]
lemma polytime_fun.zip : polytime_fun₂ (@list.zip α β) :=
begin
  inhabit α, inhabit β,
  convert_to polytime_fun₂ (λ (l₁ : list α) (l₂ : list β), (list.range $ min l₁.length l₂.length).map (λ i, (l₁.inth i, l₂.inth i))),
  { ext l₁ l₂ : 2, apply list.ext_le, { simp, }, intros n h₁ h₂, simp [list.inth], rw [list.nth_eq_some_nth_le, list.nth_eq_some_nth_le], exact ⟨rfl, rfl⟩, },
  polyfun,
end

@[simp] lemma _root_.list.map_with_index_nil {α β} (f : ℕ → α → β) :
  (@list.nil α).map_with_index f = [] := rfl

@[simp] lemma _root_.list.map_with_index_snoc {α β} (f : ℕ → α → β) (init : list α) (last : α) :
  (init ++ [last]).map_with_index f = (init.map_with_index f) ++ [f init.length last] :=
begin
  suffices : ∀ n, (init ++ [last]).map_with_index_core f n = (init.map_with_index_core f n) ++ [f (init.length + n) last],
  { exact this 0, },
  induction init with hd tl ih,
  { intro, simp [list.map_with_index_core], },
  { intro n, simp [list.map_with_index_core, ih (n + 1)], congr' 3, ring, },
end

theorem _root_.list.map_with_index_eq_zip_map {α β} (l : list α) (f : ℕ → α → β) :
  l.map_with_index f = (list.zip (list.range l.length) l).map (λ x, f x.1 x.2) :=
begin
  induction l using list.reverse_rec_on with int lst ih,
  { simp, },
  { simp [list.map_with_index_snoc, ih, list.range_succ],
    rw list.zip_append; simp, }
end

@[polyfun]
lemma polytime_fun.imap {f : α → list β} {g : α → ℕ → β → γ}
  (hf : polytime_fun f) (hg : polytime_fun₃ g) :
  polytime_fun (λ s, (f s).map_with_index (g s)) :=
begin
  convert_to polytime_fun (λ s, ((list.range $ (f s).length).zip (f s)).map (λ x, g s x.1 x.2)),
  { ext s : 1, apply list.map_with_index_eq_zip_map, },
  polyfun,
end

@[simp]
def _root_.list.attach_tails {α} : list α → list (list α)
| [] := []
| (hd :: tl) := (hd :: tl) :: (_root_.list.attach_tails tl)

@[polyfun]
lemma polytime_fun.attach_tails : polytime_fun (@list.attach_tails α) :=
begin
  convert_to polytime_fun (λ l : list α, l.map_with_index (λ i x, l.drop i)),
  { ext l : 1, rw list.map_with_index_eq_zip_map, induction l with hd tl ih,
    { simp, }, simpa [list.range_succ_eq_map,  list.zip_map_left] using ih, },
  polyfun,
end

@[simp]
def _root_.list.rec' {α β} (f : list β → α → α) (s : α) : list β → α
| [] := s
| (hd :: tl) := f (hd :: tl) (_root_.list.rec' tl)

@[polyfun]
lemma polytime_fun.list_rec {f : γ → list β → α → α} {s₀ : γ → α} {l : γ → list β}
  (hf : polytime_fun₃ f) (hs₀ : polytime_fun s₀) (hl : polytime_fun l) 
  (hb : ∃ C : polynomial ℕ, ∀ (s : γ) (l : list β) (x : α), (encode $ f s l x).sizeof ≤ (encode x).sizeof + C.eval (encode (s, l)).sizeof) :
  polytime_fun (λ s, (l s).rec' (f s) (s₀ s)) :=
begin
  convert_to polytime_fun (λ s, (l s).attach_tails.foldr (f s) (s₀ s)),
  { ext s, induction l s, { simp, }, { simp [ih], }, },
  polyfun,
  apply polysize_foldr, exact hb,
end


end list
