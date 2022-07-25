import polycodable
import npolynomial

variables {α β : Type*}

open part_eval (eval time_iter)
open polycodable (encode decode)

lemma pfun.res_mono (f : α →. β) {S S' : set α} {x y} (h : y ∈ f.res_inter S x) (hS : S ⊆ S') : y ∈ f.res_inter S' x :=
by { simp at h ⊢, tauto, }

theorem time_bound_fix {c : code} (b₁ b₂ b₃ : ℕ → ℕ) (mb : monotone b₁) 
  (h₁ : time_bound c b₁) (h₂ : ∀ x : ptree, ∃ t ≤ b₃ x.sizeof, t ∈ (time_iter ((c.eval.map ptree.to_option).res_inter {s | s.sizeof ≤ b₂ x.sizeof}) (pfun.pure 1) x)) :
  time_bound c.fix (λ t, (b₃ t) * (b₁ (b₂ t)) + t) :=
begin
  simp [time_bound, code.time], intro v, specialize h₂ v,
  rcases h₂ with ⟨t, ht, H⟩,
  obtain ⟨a, ha, a_le⟩ := @part_eval.with_time_le_of_iters_le _ (c.eval.map ptree.to_option) c.time _ _ (b₁ (b₂ v.sizeof)) _ (part_eval.time_iter_mono _ H),
  { use [a, ha], exact a_le.trans (mul_le_mul_right' ht _), },
  { intro, simp [time_dom_iff_eval_dom, pfun.map], },
  intros x y hxy, apply pfun.res_mono _ hxy, intros s hs k hk,
  refine (time_bound_spec h₁ hk).trans _, apply mb, exact hs,
end

theorem polytime_fix {c : code} (pc : polytime c) (p q : polynomial ℕ) (he : ∀ x : ptree, ∃ t ≤ p.eval x.sizeof, t ∈ time_iter ((c.eval.map ptree.to_option).res_inter {s | s.sizeof ≤ q.eval x.sizeof}) (pfun.pure 1) x) :
  polytime c.fix :=
begin
  rcases pc with ⟨f, f_le⟩, use p * (f.comp q) + polynomial.monomial 1 1, simp,
  exact time_bound_fix (λ n, f.eval n) (λ n, q.eval n) (λ n, p.eval n) (monotone_polynomial_nat _) f_le he,
end

theorem code.fix_respects [polycodable α] (c : code) (f : α →. option α) (sc : ∀ x, c.eval x = (f (decode x)).map encode) :
  part_eval.fcommutes f (c.eval.map ptree.to_option) encode :=
{ dom_of_dom := λ x, by { specialize sc (encode x), apply_fun part.dom at sc, simp at sc, simp [sc, pfun.map], },
  some_of_some := λ a b h, by { specialize sc (encode a), simp [pfun.map, sc, part.eq_some_iff.mpr h, encode], },
  none_of_none := λ a h, by { specialize sc (encode a), simp [pfun.map, sc, part.eq_some_iff.mpr h, encode], } }

theorem code.fix_respects' [polycodable α] (c : code) (f : α →. option α) (sc : ∀ x, c.eval x = (f (decode x)).map encode) :
  part_eval.fcommutes (c.eval.map ptree.to_option) f decode :=
{ dom_of_dom := λ x, by { specialize sc x, apply_fun part.dom at sc, simp at sc, simp [sc, pfun.map], },
  some_of_some := λ a b h, by { specialize sc a, simp [pfun.map, sc] at h, rcases h with ⟨a', h₁, h₂, rfl⟩, cases a', { contradiction, }, simpa [encode, ptree.of_option], },
  none_of_none := λ a h, by { specialize sc a, simp [pfun.map, sc] at h, rcases h with ⟨a', h₁, h₂⟩, cases a', assumption, { contradiction, },  } }

lemma polytime.bdd_size_decode_encode (α : Type*) [polycodable α] :
  ∃ (p : polynomial ℕ), ∀ x, (encode (decode x : α)).sizeof ≤ p.eval x.sizeof :=
begin
  obtain ⟨c, ⟨p, hp⟩, sc⟩ := polycodable.polytime_decode α, use p,
  intro x, specialize sc x, specialize hp x, rcases hp with ⟨t, H, t_le⟩,
  have := eval_sizeof_le_time (part.eq_some_iff.mp sc) H, exact this.trans t_le,
end

theorem polytime_fun.eval' [polycodable α] (f : α → option α) (g : α → α) (hf : polytime_fun f) (p q : polynomial ℕ)
  (hg : ∀ x, g x ∈ eval (f : α →. option α) x) (H : ∀ x : α, ∃ t ≤ p.eval (encode x).sizeof, t ∈ time_iter (pfun.res f {s : α | (encode s).sizeof ≤ q.eval (encode x).sizeof}) (pfun.pure 1) x) :
  polytime_fun g :=
begin
  rw polytime_fun_iff at hf, rcases hf with ⟨c, pc, sc⟩,
  use c.fix, split, swap,
  { intro x, simp, have := part_eval.frespects.eval_eq (c.fix_respects (f : α →. option α) _).to_frespects,
    simp [this, part.eq_some_iff.mpr (hg x)], simp [sc], },
  obtain ⟨P, hP⟩ := polytime.bdd_size_decode_encode α,
  apply polytime_fix pc (p.comp P) ((q.comp P) + polynomial.monomial 1 1),
  intro x, rcases H (decode x) with ⟨t, ht, t_mem⟩, refine ⟨t, ht.trans _, _⟩,
  { simp, apply monotone_polynomial_nat, apply hP, },
  have := code.fix_respects' c (f : α →. option α) _, swap, { simp [sc], }, 
  have T := λ S : set α, part_eval.eq_time_of_fcommutes (this.restrict S), simp at T, rw ← T at t_mem,
  rw part_eval.time_iter_invariant ({x} ∪ set.range (@encode α _)) at t_mem, simp at t_mem,
  apply part_eval.time_iter_mono _ t_mem,
  { intros x' y', simp, refine λ h₁ h₂ h₃, ⟨_, h₃⟩, rcases h₂ with rfl|⟨y, rfl⟩, { simp, },
    simp at h₁, apply le_add_right, refine h₁.trans _, apply monotone_polynomial_nat, apply hP, },
  { intros x' y' _, simp [sc, pfun.map], intros _ H₃, right, simp [encode] at H₃, rcases H₃ with ⟨y₂, _, rfl⟩, use y₂, },
  simp,
end

theorem polytime_fun.eval [polycodable α] [polycodable β]
  (f : β → α → option α) (g : β → α → α) (hf : polytime_fun₂ f) (p q : polynomial ℕ)
  (hg : ∀ s x, g s x ∈ eval (f s : α →. option α) x)
  (H : ∀ S x, ∃ t ≤ p.eval (encode (S, x)).sizeof, t ∈ time_iter (pfun.res (f S) {s : α | (encode (S, s)).sizeof ≤ q.eval (encode (S, x)).sizeof}) (pfun.pure 1) x) :
  polytime_fun₂ g :=
begin
  have HR : ∀ S : β, part_eval.fcommutes (f S : α →. option α) (λ s : β × α, (f s.1 s.2).map (prod.mk s.1)) (λ x, (S, x)),
  { refine λ S, ⟨_, _, _⟩, { simp, }, { simp, exact λ _ _ h, h.symm, }, { simp, }, },
  have := polytime_fun.eval' (λ s : β × α, (f s.1 s.2).map (λ r, (s.1, r))) (λ s, (s.1, g s.1 s.2)) _ p q _ _,
  { apply polytime_fun.comp polytime_fun.snd this, },
  { apply polytime_fun.option_map hf, apply polytime_fun.pair, apply polytime_fun.comp, apply polytime_fun.fst, apply polytime_fun.fst, apply polytime_fun.snd, },
  { rintro ⟨x₀, x₁⟩, simp, rw (HR x₀).to_frespects.eval_eq x₁, simp, apply hg, },
  rintro ⟨x₀, x₁⟩, rcases H x₀ x₁ with ⟨t, ht, t_mem⟩, use [t, ht],
  have HR' := (HR x₀).restrict {s : β × α | (encode s).sizeof ≤ q.eval (encode (x₀, x₁)).sizeof}, simp at HR',
  rw ← part_eval.eq_time_of_fcommutes HR', exact t_mem,
end