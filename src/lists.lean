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


lemma encode_list_def (x : list ptree) : polycodable.encode x = ptree.equiv_list.symm x := rfl

lemma polytime_fun.head : polytime_fun (@list.head ptree _) :=
⟨code.left, polytime_left,
by { intro x, cases x; simp [encode], refl, }⟩

lemma polytime_fun.tail : polytime_fun (@list.tail ptree) :=
⟨code.right, polytime_right,
by { intro x, cases x; simp [encode], }⟩

lemma polytime_fun.cons : polytime_fun₂ (@list.cons ptree) :=
⟨code.id, polytime_id,
by { intro x, dunfold polycodable.encode, cases x; simp [encode], }⟩

variables {α β : Type*} [polycodable α] [polycodable β]
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

lemma len_le_encode_sizeof (a : list ptree) :
  a.length + 1 ≤ (encode a).sizeof :=
by { induction a with hd tl ih, { simp, }, simp, linarith, }


def polysize_fun (f : α → β) : Prop :=
∃ p : polynomial ℕ, ∀ (x : α), (encode (f x)).sizeof ≤ p.eval (encode x).sizeof

lemma polysize_of_polytime_fun (f : α → β) (hf : polytime_fun f) :
  polysize_fun f :=
begin
  rcases hf with ⟨c, ⟨p, hp⟩, sc⟩, use p,
  intro x, specialize sc x, rw part.eq_some_iff at sc,
  rcases hp (encode x) with ⟨t, ht, t_le⟩,
  exact (eval_sizeof_le_time sc ht).trans t_le,
end

end encode_sizeof

theorem polytime_fun.foldl (f : β → α → ptree → α) (l : β → list ptree) (acc : β → α) 
  (hf : polytime_fun₃ f) (hl : polytime_fun l) (hacc : polytime_fun acc) 
  (hs : polysize_fun (λ xls : β × α × list ptree, xls.2.2.foldl (f xls.1) xls.2.1)) :
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

end list
