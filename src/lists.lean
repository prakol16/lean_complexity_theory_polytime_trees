import polyfix
import polysize
import data.list.basic

section foldl
variables {α γ : Type*}

def tails_foldl_step (f : α → list γ → α) (x : list γ × α) : bool × (list γ × α) :=
(x.1.empty, x.1.tail, f x.2 x.1)

variables (f : α → list γ → α) (x : list γ × α)
lemma tails_foldl_step_iter :
  iterator_evaln (tails_foldl_step f) (2 + x.1.length) (ff, x) = some ([], x.1.tails.foldl f x.2) :=
begin
  cases x with l x,
  induction l with hd tl ih generalizing x,
  { simp [tails_foldl_step], }, { simp [tails_foldl_step, ← add_assoc, ih], },
end

variables {f}
lemma tails_foldl_states_suffix {s₀ s : bool × list γ × α} (hs : s ∈ (mk_iterator ↑(tails_foldl_step f) s₀).states) :
  s.2.1 <:+ s₀.2.1 :=
begin
  rcases s₀ with ⟨b₀, l₀, s₀⟩,
  apply execution.step_induction hs; clear hs s,
  { simp, },
  rintros ⟨b, l, s⟩ ⟨b', l', s'⟩ _, simp,
  rintros ih rfl, simp [tails_foldl_step],
  rintros rfl rfl rfl,
  exact l.tail_suffix.trans ih,
end

end foldl

section
open ptree.pencodable (encode decode)
variables {α β γ : Type*} [polycodable α] [polycodable β] [polycodable γ]
  {f : β → α → list γ → α} {l : β → list γ} (acc : β → α) 

lemma acc_list_polysize_fun_uniform (hl : polysize_fun l) :
  polysize_fun_uniform (λ (s : β) (y : (mk_iterator ↑(tails_foldl_step (f s)) (ff, l s, acc s)).states), (y : bool × list γ × α).2.1) :=
begin
  rcases hl with ⟨pi, hpi⟩, use pi, intros s x,
  refine trans (encode_sizeof_le_of_infix _) (hpi _),
  exact (tails_foldl_states_suffix (subtype.mem x)).is_infix,
end

lemma tails_foldl_polysize_safe (hinit : polysize_fun l)
  (hf : polysize_fun_safe (λ (s : β × list γ) (x : α), f s.1 x s.2)) :
  polysize_fun_safe (λ (s : β) (y : (mk_iterator ↑(tails_foldl_step (f s)) (ff, l s, acc s)).states), tails_foldl_step (f s) (y : bool × list γ × α).2) :=
begin
  dsimp only [tails_foldl_step] at *,
  apply polysize_fun_safe.pair_left, { apply polysize_uniform_of_fin_range, },
  apply polysize_fun_safe.pair_left,
  { apply polysize_fun_uniform.comp' (polysize_fun_safe.tail _),
    apply acc_list_polysize_fun_uniform _ hinit, },
  change polysize_fun_safe (λ x y, (λ (s : β × list γ) (x : α), f s.1 x s.2) (x, (↑y : bool × list γ × α).2.1) (↑y : bool × list γ × α).2.2),
  apply polysize_fun_safe.comp hf,
  { apply polysize_fun_uniform.pair, { simpa using polysize_fun.id, }, apply acc_list_polysize_fun_uniform _ hinit, },
  refine polysize_fun_safe.comp' (polysize_fun_safe.snd _) _, refine polysize_fun_safe.comp' (polysize_fun_safe.snd _) _,
  use 0, intros, simp [penc_states_encode],
end

end

section list

variables {α β γ : Type*} [polycodable α] [polycodable β] [polycodable γ]
open ptree.pencodable (encode decode)

variable (H_enc : polytime_fun (λ l : ptree, ptree.equiv_list.symm $ l.equiv_list.map (encode ∘ (@decode γ _))))

def inh : inhabited γ := ⟨decode ptree.nil⟩ 
local attribute [instance] inh

include H_enc
-- List encoding aux; used very frequently, so better have a short name
def lea : polycodable (list γ) :=
{ polytime_decode := by simpa [encode, decode] using H_enc }

lemma polytime_fun.head_aux : polytime_fun (@list.head γ _) :=
by { letI := lea H_enc, rw polytime_fun_iff', use [code.left, polytime_left], intro x, cases x, { simp, refl, }, simp [ptree.pencodable.encode_list_def], }

lemma polytime_fun.tail_aux : polytime_fun (@list.tail γ) :=
⟨code.right, polytime_right,
by { intro x, cases x; simp [encode, decode], }⟩

lemma polytime_fun.cons_aux : polytime_fun₂ (@list.cons γ) :=
⟨code.id, polytime_id,
by { intro x, cases x; simp [encode], }⟩

lemma polytime_fun.is_empty_aux : polytime_fun (@list.empty γ) :=
by { letI := lea H_enc, classical, convert_to polytime_fun (λ l : list γ, (l = [] : bool)), { ext x, cases x; simp, }, polyfun, }

lemma polytime_fun.foldl_tails_aux {f : β → α → list γ → α} {l : β → list γ} {acc : β → α}
  (hf : polytime_fun₃ f) (hl : polytime_fun l) (hacc : polytime_fun acc)
  (hs : polysize_fun_safe (λ (a : β × list γ) (b : α), f a.1 b a.2)) :
  polytime_fun (λ s, (l s).tails.foldl (f s) (acc s)) :=
begin
  letI := lea H_enc,
  suffices : polytime_fun (λ s, (@list.nil γ, (l s).tails.foldl (f s) (acc s))), { exact polytime_fun.snd.comp this, },
  apply polytime_fun.evaln_of_polysize (λ (s : β) (x : list γ × α), tails_foldl_step (f s) x) (λ x, (ff, l x, acc x)) (λ s, 2 + (l s).length),
  { dunfold tails_foldl_step, have := polytime_fun.tail_aux H_enc, have := polytime_fun.is_empty_aux H_enc, polyfun, },
  { polyfun, }, rotate 1,
  { obtain ⟨q, hq⟩ := polysize_of_polytime_fun hl, use 2 + q, intros s, simpa using (len_le_encode_sizeof _).trans (hq _), },
  { intro s, simpa using tails_foldl_step_iter (f s) (l s, acc s), },
  exact tails_foldl_polysize_safe _ (polysize_of_polytime_fun hl) hs,
end

lemma polytime_fun.foldl_aux {f : β → α → γ → α} {l : β → list γ} {acc : β → α}
  (hf : polytime_fun₃ f) (hl : polytime_fun l) (hacc : polytime_fun acc)
  (hs : polysize_fun_safe (λ (a : β × γ) (b : α), f a.1 b a.2)) :
  polytime_fun (λ s, (l s).foldl (f s) (acc s)) :=
begin
  letI := lea H_enc,
  convert_to polytime_fun (λ s, (l s).tails.foldl (λ (a : α) (ls : list γ), if ls.empty then a else f s a ls.head) (acc s)),
  { ext s, generalize : acc s = a, induction l s with hd tl ih generalizing a, { simp, }, simp [ih], },
  apply polytime_fun.foldl_tails_aux H_enc,
  { have := polytime_fun.head_aux H_enc, have := polytime_fun.is_empty_aux H_enc, polyfun, },
  { exact hl, }, { exact hacc, },
  apply polysize_fun_safe.ite, { apply polysize_fun_safe.id, }, 
  change polysize_fun_safe (λ (x : β × list γ) (y : α), (λ (a : β × γ) (b : α), f a.1 b a.2) (x.1, x.2.head) y),
  apply hs.comp, { have := polytime_fun.head_aux H_enc, simp, apply polysize_of_polytime_fun, polyfun, }, { exact polysize_fun_safe.id, },
end

lemma polytime_fun.reverse_aux : polytime_fun (@list.reverse γ) :=
begin
  letI := lea H_enc,
  convert_to polytime_fun (λ l : list γ, l.foldl (λ acc hd, hd :: acc) []),
  { ext l : 1, rw ← list.foldr_reverse, simp, },
  apply polytime_fun.foldl_aux H_enc, { have := polytime_fun.cons_aux H_enc, polyfun, }, { polyfun, }, { polyfun, },
  apply polysize_fun_safe.comp polysize_fun_safe.cons, { simp, apply polysize_of_polytime_fun, polyfun, }, exact polysize_fun_safe.id,
end

lemma polytime_fun.foldr_aux {f : β → γ → α → α} {l : β → list γ} {acc : β → α}
  (hf : polytime_fun₃ f) (hl : polytime_fun l) (hacc : polytime_fun acc)
  (hs : polysize_fun_safe (λ (a : β × γ) (b : α), f a.1 a.2 b)) :
  polytime_fun (λ s, (l s).foldr (f s) (acc s)) :=
begin
  letI := lea H_enc,
  simp only [← list.foldl_reverse],
  apply polytime_fun.foldl_aux H_enc, { polyfun, }, { have := polytime_fun.reverse_aux H_enc, polyfun, }, { polyfun, },
  exact hs,
end

lemma polytime_fun.map_aux 
  (H_enc' : polytime_fun (λ l : ptree, ptree.equiv_list.symm $ l.equiv_list.map (encode ∘ (@decode α _))))
  {f : β → γ → α} {l : β → list γ} (hf : polytime_fun₂ f) (hl : polytime_fun l) :
  polytime_fun (λ s, (l s).map (f s)) :=
begin
  letI := lea H_enc, letI := lea H_enc',
  convert_to polytime_fun (λ s, (l s).foldr (λ hd acc, (f s hd) :: acc) []),
  { ext s : 1, induction l s with hd tl ih, { simp, }, simp [ih], },
  apply polytime_fun.foldr_aux H_enc,
  { have := polytime_fun.cons_aux H_enc', polyfun, }, { exact hl, }, { polyfun, },
  apply polysize_fun_safe.comp polysize_fun_safe.cons, { simp, apply polysize_of_polytime_fun, exact hf, }, { exact polysize_fun_safe.id, },
end

end list


section list_ptree
open ptree.pencodable (encode decode)

def list_ptree_encode : polycodable (list ptree) :=
lea ⟨code.id, polytime_id, by simp [encode, decode]⟩

local attribute [instance] list_ptree_encode

@[polyfun]
lemma polytime_fun.equiv_list : polytime_fun ptree.equiv_list :=
⟨_, polytime_id, by simp [encode]⟩

@[polyfun]
lemma polytime_fun.equiv_list_symm : polytime_fun ptree.equiv_list.symm :=
⟨_, polytime_id, by simp [encode]⟩

lemma H_enc {γ : Type*} [polycodable γ] : 
  polytime_fun (λ l : ptree, ptree.equiv_list.symm $ l.equiv_list.map (encode ∘ (@decode γ _))) :=
begin
  refine polytime_fun.equiv_list_symm.comp (polytime_fun.comp _ polytime_fun.equiv_list),
  apply polytime_fun.map_aux, iterate 2 { simpa using polytime_fun.id, },
  { /- TODO: Debug -/ dunfold polytime_fun₂ function.uncurry, apply polytime_fun.comp; polyfun, }, polyfun,
end

end list_ptree

section list
open ptree.pencodable (encode decode)

variables {α β γ : Type*} [polycodable α] [polycodable β] [polycodable γ]
instance : polycodable (list α) :=
lea H_enc


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

lemma polytime_fun.foldl_tails {f : β → α → list γ → α} {l : β → list γ} {acc : β → α}
  (hf : polytime_fun₃ f) (hl : polytime_fun l) (hacc : polytime_fun acc)
  (hs : polysize_fun_safe (λ (a : β × list γ) (b : α), f a.1 b a.2)) :
  polytime_fun (λ s, (l s).tails.foldl (f s) (acc s)) := polytime_fun.foldl_tails_aux H_enc hf hl hacc hs

@[polyfun]
lemma polytime_fun.foldl {f : β → α → γ → α} {l : β → list γ} {acc : β → α}
  (hf : polytime_fun₃ f) (hl : polytime_fun l) (hacc : polytime_fun acc)
  (hs : polysize_fun_safe (λ (a : β × γ) (b : α), f a.1 b a.2)) :
  polytime_fun (λ s, (l s).foldl (f s) (acc s)) := polytime_fun.foldl_aux H_enc hf hl hacc hs

@[polyfun]
lemma polytime_fun.reverse : polytime_fun (@list.reverse γ) := polytime_fun.reverse_aux H_enc

@[polyfun]
lemma polytime_fun.foldr {f : β → γ → α → α} {l : β → list γ} {acc : β → α}
  (hf : polytime_fun₃ f) (hl : polytime_fun l) (hacc : polytime_fun acc)
  (hs : polysize_fun_safe (λ (a : β × γ) (b : α), f a.1 a.2 b)) :
  polytime_fun (λ s, (l s).foldr (f s) (acc s)) := polytime_fun.foldr_aux H_enc hf hl hacc hs

@[polyfun]
lemma polytime_fun.map 
  {f : β → γ → α} {l : β → list γ} (hf : polytime_fun₂ f) (hl : polytime_fun l) :
  polytime_fun (λ s, (l s).map (f s)) := polytime_fun.map_aux H_enc H_enc hf hl

@[polyfun]
lemma polytime_fun.filter {f : β → γ → bool} {l : β → list γ} (hf : polytime_fun₂ f) (hl : polytime_fun l) :
  polytime_fun (λ s, (l s).filter (λ x, f s x)) :=
begin
  convert_to polytime_fun (λ s, (l s).foldr (λ hd acc, if f s hd then hd :: acc else acc) []),
  { ext s : 1, induction l s with hd tl ih, { simp, }, cases H : f s hd; simpa [H], },
  polyfun, apply polysize_fun_safe.ite, { refine polysize_fun_safe.comp polysize_fun_safe.cons _ polysize_fun_safe.id, simp, exact polysize_of_polytime_fun polytime_fun.snd, }, exact polysize_fun_safe.id,
end

@[polyfun]
lemma polytime_fun.append : polytime_fun₂ (λ (l₁ l₂ : list α), l₁ ++ l₂) :=
begin
  convert_to polytime_fun₂ (λ (l₁ l₂ : list α), l₁.foldr list.cons l₂),
  { ext l₁ l₂ : 2, induction l₁ with hd tl ih, { simp, }, { simp [ih], } },
  polyfun, apply polysize_fun_safe.cons.comp, { simp, apply polysize_of_polytime_fun polytime_fun.snd, }, exact polysize_fun_safe.id,
end

@[polyfun]
lemma polytime_fun.tails : polytime_fun (@list.tails α) :=
begin
  convert_to polytime_fun (λ l : list α, (l.tails.foldl (λ acc x, x :: acc) []).reverse),
  { simp, }, apply polytime_fun.comp, { polyfun, }, apply polytime_fun.foldl_tails,
  { polyfun, }, { polyfun, }, { polyfun, }, apply polysize_fun_safe.cons.comp, { simp, apply polysize_of_polytime_fun polytime_fun.snd, }, exact polysize_fun_safe.id,
end


def unary_nat_encode : polycodable ℕ := 
polycodable.of_equiv equiv.list_unit_equiv.symm

local attribute [instance] unary_nat_encode

lemma unary_nat_encode_eq (n : ℕ) : encode n = encode (list.repeat () n) := rfl

@[polyfun]
lemma polytime_fun.unary_length : polytime_fun (@list.length α) :=
begin
  convert_to polytime_fun (λ l : list α, equiv.list_unit_equiv (l.map (λ _, ()))),
  { ext l, simp [equiv.list_unit_equiv], }, polyfun, exact polycodable.of_equiv_polytime_symm _,
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

lemma _root_.list.drop_succ {α : Type*} (l : list α) (n : ℕ) :
  l.drop (n+1) = l.tail.drop n :=
by { induction l; simp, }

@[polyfun]
lemma polytime_fun.drop : polytime_fun₂ (@list.drop α) :=
begin
  convert_to polytime_fun₂ (λ (n : ℕ) (l : list α), (list.repeat () n).foldr (λ _ (l' : list α), l'.tail) l),
  { ext n l : 2, rw list.foldr_const, simp, induction n generalizing l; simp [list.drop_succ, *], },
  polyfun, exact polysize_fun_safe.tail _,
end

@[polyfun]
lemma polytime_fun.nth : polytime_fun₂ (@list.nth α) :=
begin
  convert_to polytime_fun₂ (λ (l : list α) n, (l.drop n).head'),
  { ext l n : 2, simp [← list.nth_zero, list.nth_drop], },
  polyfun,
end

@[polyfun]
lemma polytime_fun.tsub : polytime_fun₂ (@has_sub.sub ℕ _) :=
begin
  convert_to polytime_fun₂ (λ (m n : ℕ), ((list.repeat () m).drop n).length),
  { ext m n, simp, }, polyfun,
end

@[polyfun]
lemma polytime_fun.last : polytime_fun (@list.last' α) :=
by { convert_to polytime_fun (λ l : list α, l.reverse.head'), { ext l : 1, induction l using list.reverse_rec_on; simp, }, polyfun, }

@[polyfun]
lemma polytime_fun.filter_map {f : β → α → option γ} {l : β → list α} 
  (hf : polytime_fun₂ f) (hl : polytime_fun l) :
  polytime_fun (λ s, (l s).filter_map (f s)) :=
begin
  inhabit γ,
  convert_to polytime_fun (λ s, (((l s).map (λ x, f s x)).filter (λ x : option γ, x.is_some)).map option.iget),
  { ext s : 1, induction l s with hd tl ih, { simp, }, cases H : f s hd, { simpa [H], }, { simpa [list.filter_map_cons_some _ _ _ H, H], } },
  polyfun,
end

@[simp] lemma _root_.list.filter_map_none (l : list α) :
  l.filter_map (λ _, (none : option β)) = [] :=
by { induction l; simp [*], }

lemma zip_eq_inits_map [inhabited α] (l₁ : list α) (l₂ : list β) :
  l₁.zip l₂ = l₁.inits.tail.filter_map (λ x, (l₂.nth (x.length - 1)).map (λ y, (x.last'.iget, y))) :=
begin
  induction l₁ with hd tl ih generalizing l₂,
  { simp, },
  cases l₂ with h₂ t₂, { simp, }, 
  simp [list.filter_map_map, function.comp], 
  cases tl, { simp, rw list.filter_map_cons_some, { simp, }, simp, },
  simp, rw list.filter_map_cons_some, swap, { simp, },
  rw ih t₂, simp [list.filter_map_map, function.comp],
end

@[polyfun]
lemma polytime_fun.inits : polytime_fun (@list.inits α) :=
by { convert_to polytime_fun (λ l : list α, (l.reverse.tails.map list.reverse).reverse), { simp [list.tails_reverse], }, polyfun, }

@[polyfun]
lemma polytime_fun.zip : polytime_fun₂ (@list.zip α β) :=
begin
  inhabit α,
  change polytime_fun₂ (λ l₁ l₂, list.zip l₁ l₂), simp_rw zip_eq_inits_map, polyfun,
end

@[polyfun]
lemma polytime_fun.all {f : β → α → bool} {l : β → list α} 
  (hf : polytime_fun₂ f) (hl : polytime_fun l) : polytime_fun (λ s, (l s).all (f s)) :=
by { dunfold list.all, polyfun, exact (polysize_uniform_of_fin_range _).to_safe, }

@[polyfun]
lemma polytime_fun.unary_nat_le {f g : β → ℕ} (hf : polytime_fun f) (hg : polytime_fun g) :
  polytime_fun (λ s, ((f s) ≤ (g s) : bool)) :=
by { convert_to polytime_fun (λ s, ((f s) - (g s) = 0 : bool)), { simp, }, polyfun, }

end list

