import polycodable
import npolynomial
import promise
import polysize

variables {α β : Type*}

open ptree.pencodable (encode decode)

theorem fix_time_le {c : code} {x₀ : ptree} {N : ℕ} (b₁ b₂ : ℕ → ℕ) (mb : monotone b₁) 
  (h₁ : time_bound c b₁) (h₂ : ∀ {x : ptree}, x ∈ (c.fix_iterator x₀).states → x.sizeof ≤ b₂ x₀.sizeof) 
  (hN : N ∈ (c.fix_iterator x₀).time (pfun.pure 1)) :
  ∃ t ∈ c.fix.time x₀, t ≤ (b₁ (b₂ x₀.sizeof)) * N + x₀.sizeof :=
begin
  simp [code.time],
  refine execution.time_le (c.fix_iterator x₀) (b₁ (b₂ x₀.sizeof)) c.time _ _ hN,
  { intros, rw time_dom_iff_eval_dom, change x ∈ c.eval.dom, rw eval_dom_of_time_bound h₁, triv, },
  intros x t hx ht,
  rcases h₁ x with ⟨t, tmp, ht'⟩, cases part.mem_unique ht tmp,
  exact ht'.trans (mb (h₂ hx)),
end

theorem polytime_fix_on_pred {c : code} (pc : polytime c) (pred : set ptree)
  (hs : ∃ p : polynomial ℕ, ∀ {x₀ x : ptree}, x₀ ∈ pred → x ∈ (c.fix_iterator x₀).states → x.sizeof ≤ p.eval x₀.sizeof)
  (hn : ∃ q : polynomial ℕ, ∀ {x₀ : ptree}, x₀ ∈ pred → ∃ N ∈ (c.fix_iterator x₀).time (pfun.pure 1), N ≤ q.eval x₀.sizeof) :
  polytime_promise c.fix pred  :=
begin
  cases pc with f pc, cases hs with p hs, cases hn with q hn, use (f.comp p) * q + polynomial.monomial 1 1, simp,
  intros v hv, rcases hn hv with ⟨N, hN, N_le⟩,
  obtain ⟨t, ht, t_le⟩ := fix_time_le (λ n, f.eval n) (λ n, p.eval n) (monotone_polynomial_nat _) pc (λ _, hs hv) hN,
  refine ⟨t, ht, t_le.trans _⟩, mono*; exact zero_le',
end

theorem polytime_fix {c init : code} (pc : polytime c) (pinit : polytime init)
  (hs : ∃ p : polynomial ℕ, ∀ {x₀ x : ptree}, x ∈ (c.fix_iterator (pinit.to_fun x₀)).states → x.sizeof ≤ p.eval (pinit.to_fun x₀).sizeof)
  (hn : ∃ q : polynomial ℕ, ∀ (x₀ : ptree), ∃ N ∈ (c.fix_iterator (pinit.to_fun x₀)).time (pfun.pure 1), N ≤ q.eval (pinit.to_fun x₀).sizeof) :
  polytime (c.fix.comp init) :=
begin
  have ran_eq : init.eval.ran = set.range pinit.to_fun,
  { ext, simp [pfun.mem_ran_iff, part.get_eq_iff_mem], },
  simpa [← ran_eq, pinit.dom_univ] using polytime_promise_comp (polytime_fix_on_pred pc (set.range pinit.to_fun) _ _) (polytime_promise.univ.mpr pinit),
  { cases hs with p hs, use p, rintros x₀ x' ⟨x, rfl⟩ hx', exact hs hx', },
  { cases hn with q hn, use q, rintros x₀ ⟨x, rfl⟩, apply hn, },
end

-- @[simps]
def mk_iterator {α} (f : α →. bool × α) (x₀ : bool × α) : execution (bool × α) :=
{ next := λ x, if x.1 = tt then (part.some none) else ((f x.2).map some),
  start := x₀ }

@[simp] lemma mk_iterator_some {f : α →. bool × α} {x₀ x x' : bool × α} :
  some x' ∈ (mk_iterator f x₀).next x ↔ x.1 = ff ∧ x' ∈ f x.2 :=
by { simp only [mk_iterator], split_ifs with h, { simp [h], }, rw bool_iff_false at h, simp [-prod.exists, h, and_comm], }

@[simp] lemma mk_iterator_none {f : α →. bool × α} {x₀ x : bool × α} :
  none ∈ (mk_iterator f x₀).next x ↔ x.1 = tt :=
by { simp only [mk_iterator], split_ifs with h; simp [h], }

@[simp] lemma mk_iterator_dom {f : α →. bool × α} {x₀ x : bool × α} :
  ((mk_iterator f x₀).next x).dom ↔ x.1 = tt ∨ (f x.2).dom :=
by simp [mk_iterator, apply_ite part.dom]

@[simp] lemma mk_iterator_start {f : α →. bool × α} {x₀ : bool × α} : (mk_iterator f x₀).start = x₀ := rfl

@[simp] lemma mk_iterator_change_start {f : α →. bool × α} {x₀ x₀' : bool × α} :
  (execution.mk (mk_iterator f x₀).next x₀') = (mk_iterator f x₀') :=
by { ext : 1; simp, refl, } 

@[simp] lemma some_eq_ite_none_some {α} (P : Prop) [decidable P] (a b : α) :
  (some a = if P then none else some b) ↔ ¬P ∧ a = b :=
by { split_ifs; simp; tauto, }

@[simp] lemma none_eq_ite_none_some {α} (P : Prop) [decidable P] (b : α) :
  (none = if P then none else some b) ↔ P := by { split_ifs; simpa, }

@[simps]
def code.fix_respects [ptree.pencodable α] (c : code) (f : α → bool × α) (sc : ∀ x : bool × α, c.eval (encode x) = part.some (encode (f x.2))) (x₀ : bool × α) :
  (mk_iterator ↑f x₀) ∼ₛ (c.fix_iterator (encode x₀)) :=
{ rel := λ x ex, ex = encode x,
  dom_iff := λ _ _ _ _, by { rintro rfl, conv_lhs { simp, }, conv_rhs { simp [code.fix_iterator, sc, apply_ite part.dom], }, },
  some_iff := λ x ex x' ex' _ _, by { rintro rfl, cases x, simp [sc], rintros rfl rfl _, exact id, },
  none_iff := λ x ex hx hex, by { rintro rfl, cases x with x₁ x₂, simp [encode], cases x₁; simp, },
  start := rfl }

theorem polytime_fun.eval' {α β} [polycodable α] [polycodable β] (f : α → bool × α) (init : β → bool × α)
  (hf : polytime_fun f) (hinit : polytime_fun init)
  (hs : ∃ p : polynomial ℕ, ∀ {x₀ x}, x ∈ (mk_iterator ↑f (init x₀)).states → (encode x).sizeof ≤ p.eval (encode $ init x₀).sizeof)
  (hn : ∃ q : polynomial ℕ, ∀ x₀, ∃ N ∈ (mk_iterator ↑f (init x₀)).time (pfun.pure 1), N ≤ q.eval (encode $ init x₀).sizeof)
  (g : β → α) (hg : ∀ x, (tt, g x) ∈ (mk_iterator ↑f (init x)).eval) : polytime_fun g :=
begin
  suffices : polytime_fun (λ x, (tt, g x)), { exact polytime_fun.snd.comp this, },
  obtain ⟨c, pc, sc⟩ : polytime_fun (λ x : bool × α, f x.2) := by polyfun,
  let R := code.fix_respects c f sc,
  rw polytime_fun_iff at hinit, rcases hinit with ⟨ci, pci, sci⟩,
  use c.fix.comp ci, split,
  { apply polytime_fix pc pci,
    { cases hs with p hs, simp [sci],
      use p, intros x₀ x hx, 
      obtain ⟨x, hy, hrel⟩ := (R (init (decode x₀))).symm.exists_state_of hx,
      simp at hrel, subst hrel, exact hs hy, },
    { cases hn with q hn, simp [sci], 
      use q, intros x₀, specialize R (init (decode x₀)), specialize hn (decode x₀),
      simpa [R.time_pure_eq] using hn, } },
  intro x, simp [sci], rw ← code.fix_iterator,
  simpa [part.eq_some_iff] using (R (init x)).mem_eval_of (hg x),
end

@[simps]
def curry_state {α β} (f : β → α → bool × α) (x : β) (y : bool × α) :
  (mk_iterator ↑(f x) y) ∼ₛ (mk_iterator ↑(λ x' : β × α, ((f x'.1 x'.2).1, x'.1, (f x'.1 x'.2).2)) (y.1, x, y.2)) :=
{ rel := λ a b, b = (a.1, x, a.2),
  dom_iff := by { intros, simp, },
  some_iff := λ a b a' b' _ _, by { rintro rfl, simp, rintros _ rfl _ rfl, refl, },
  none_iff := λ a a' _ _, by { rintro rfl, simp, },
  start := rfl }

theorem polytime_fun.eval {α β} [polycodable α] [polycodable β] {f : β → α → bool × α} {init : β → bool × α}
  (hf : polytime_fun₂ f) (hinit : polytime_fun init)
  (hs : ∃ p : polynomial ℕ, ∀ {x₀ x}, x ∈ (mk_iterator ↑(f x₀) (init x₀)).states → (encode x).sizeof ≤ p.eval (encode x₀).sizeof)
  (hn : ∃ q : polynomial ℕ, ∀ x₀, ∃ N ∈ (mk_iterator ↑(f x₀) (init x₀)).time (pfun.pure 1), N ≤ q.eval (encode x₀).sizeof)
  (g : β → α) (hg : ∀ x, (tt, g x) ∈ (mk_iterator ↑(f x) (init x)).eval) : polytime_fun g :=
begin
  suffices : polytime_fun (λ x : β, (x, g x)), { apply polytime_fun.snd.comp this, },
  let R := curry_state f,
  apply polytime_fun.eval' (λ x : β × α, ((f x.1 x.2).1, x.1, (f x.1 x.2).2)) (λ x : β, ((init x).1, x, (init x).2)),
  { polyfun, }, { polyfun, },
  { cases hs with p hs, use p + polynomial.monomial 1 1, 
    rintros x₀ ⟨b, x₀', s⟩ H,
    obtain ⟨⟨b', s'⟩, h₁, h₂⟩ := (R x₀ (init x₀)).symm.exists_state_of H,
    simp at h₂, rcases h₂ with ⟨rfl, rfl, rfl⟩,
    specialize hs h₁, simp at hs ⊢, 
    ac_change ((encode b).sizeof + (encode s).sizeof + 1) + ((encode x₀').sizeof + 1) ≤ _,
    mono, { refine hs.trans _, apply monotone_polynomial_nat, linarith only, }, { linarith only, }, },
  { cases hn with q hn, use q, intros x₀,
    simp_rw (R x₀ (init x₀)).symm.time_pure_eq,
    rcases hn x₀ with ⟨N, h, N_le⟩, refine ⟨N, h, N_le.trans _⟩,
    simp, apply monotone_polynomial_nat, linarith only, },
  intro x,
  obtain ⟨⟨r₁, r₂, r₃⟩, hr₁, hr₂⟩ := (R x (init x)).mem_eval_of (hg x),
  simp at hr₂, rcases hr₂ with ⟨rfl, rfl, rfl⟩, exact hr₁,
end

noncomputable theory
open_locale classical

noncomputable instance {σ : Type*} [polycodable σ] (f : execution σ) : ptree.pencodable f.states :=
set_encodable _ f.start_mem_states

theorem polytime_fun.eval_of_polysize {α β} [polycodable α] [polycodable β] {f : β → α → bool × α} {init : β → bool × α}
  (hf : polytime_fun₂ f) (hinit : polytime_fun init)
  (hfs : polysize_fun_safe (λ (x₀ : β) (y : (mk_iterator ↑(f x₀) (init x₀)).states), f x₀ (y : bool × α).2))
  (hn : ∃ q : polynomial ℕ, ∀ x₀, ∃ N ∈ (mk_iterator ↑(f x₀) (init x₀)).time (pfun.pure 1), N ≤ q.eval (encode x₀).sizeof) 
  (g : β → α) (hg : ∀ x, (tt, g x) ∈ (mk_iterator ↑(f x) (init x)).eval) : polytime_fun g :=
begin
  refine polytime_fun.eval hf hinit _ hn g hg,
  rcases hfs with ⟨p, hp⟩, rcases hn with ⟨q, hn⟩, dsimp only at hp,
  obtain ⟨p₂, hp₂⟩ := polysize_of_polytime_fun hinit,
  use p₂ + p * q, intros x₀,
  suffices : ∀ (s : ℕ × bool × α), s ∈ ((mk_iterator ↑(f x₀) (init x₀)).time_with (pfun.pure 1)).states → (encode s.2).sizeof ≤ p₂.eval (encode x₀).sizeof + (p.eval (encode x₀).sizeof) * s.1,
  { intros s hs, 
    obtain ⟨⟨t, s'⟩, h₁, h₂⟩ := (execution.time_with_tr (mk_iterator ↑(f x₀) (init x₀)) (pfun.pure 1) (by simp)).exists_state_of hs,
    simp at h₂, subst h₂,
    specialize this _ h₁, specialize hn x₀, specialize hp x₀, simp at this ⊢,
    refine this.trans _,
    mono*, any_goals { exact zero_le' },
    rcases hn with ⟨N, hN, N_le⟩,
    exact (execution.state_time_le_time _ _ hN h₁).trans N_le, },
  intros s hs, apply execution.step_induction hs,
  { specialize hp₂ x₀, simpa [execution.time_with], },
  rintros ⟨t, s⟩ ⟨t', s'⟩ hs ih,
  simp [execution.time_with, ← apply_ite part.some],
  rintros rfl _ rfl,
  specialize hp x₀ ⟨s, _⟩,
  { obtain ⟨⟨_, s'⟩, h₁, h₂⟩ := (execution.time_with_tr (mk_iterator ↑(f x₀) (init x₀)) (pfun.pure 1) (by simp)).symm.exists_state_of hs, simp at h₂, rwa ← h₂, },
  refine hp.trans _, rw [add_comm 1 t, mul_add], simp [← add_assoc], 
  exact ih.trans rfl.le,
end

@[simp]
def iterator_evaln {α : Type*} (f : α → bool × α) : ℕ → bool × α → option α
| 0 _ := none
| (n+1) (b, x) := cond b (some x) (iterator_evaln n (f x))

lemma eval_of_iterator_evaln {α} {f : α → bool × α} {N : ℕ} {x₀ : bool × α} {y : α}
  (hy : y ∈ iterator_evaln f N x₀) : ∃ n ≤ N, (n, tt, y) ∈ ((mk_iterator ↑f x₀).time_with (pfun.pure 1)).eval :=
begin
  induction N with N ih generalizing x₀, { contradiction, },
  cases x₀ with b₀ x₀,
  cases b₀, swap,
  { refine ⟨0, zero_le', _⟩, rw [execution.time_with, execution.mem_eval],
    simp at hy, subst hy, split, { exact execution.start_mem_states _, }, simp, },
  simp at hy, specialize ih hy, rcases ih with ⟨n, H, n_mem⟩,
  refine ⟨n+1, _, _⟩, { simpa [nat.succ_eq_add_one], },
  rw ← @execution.eval_from _ _ (1, f x₀), swap,
  { apply execution.mem_states_of_fwd (execution.start_mem_states _), simp [execution.time_with], },
  simp only [execution.time_with], rw track_with_change_start,
  simp,
  have := (mk_iterator ↑f (f x₀)).time_fwd (pfun.pure 1) 1, simp at this, rw this,
  rw ← part.eq_some_iff at n_mem, simp [n_mem],
end

theorem polytime_fun.evaln_of_polysize {α β} [polycodable α] [polycodable β] {f : β → α → bool × α} {init : β → bool × α}
  (hf : polytime_fun₂ f) (hinit : polytime_fun init) (N : β → ℕ)
  (hfs : polysize_fun_safe (λ (x₀ : β) (y : (mk_iterator ↑(f x₀) (init x₀)).states), f x₀ (y : bool × α).2))
  (hn : ∃ q : polynomial ℕ, ∀ x₀, N x₀ ≤ q.eval (encode x₀).sizeof) 
  (g : β → α) (hg : ∀ x, g x ∈ iterator_evaln (f x) (N x) (init x)) : polytime_fun g :=
begin
  refine polytime_fun.eval_of_polysize hf hinit hfs _ g _,
  { rcases hn with ⟨q, hn⟩, use q, intros x₀, 
    obtain ⟨n, n_le, hn'⟩ := eval_of_iterator_evaln (hg x₀),
    use n, refine ⟨_, n_le.trans (hn _)⟩,
    simp only [execution.time], rw ← part.eq_some_iff at hn', simp [hn'], },
  intros x₀,
  obtain ⟨_, _, hn'⟩ := eval_of_iterator_evaln (hg x₀),
  obtain ⟨y, hy, hrel⟩ := (execution.time_with_tr (mk_iterator ↑(f x₀) (init x₀)) (pfun.pure 1) (by simp)).symm.mem_eval_of hn',
  simp at hrel, rwa ← hrel,
end
