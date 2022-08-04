import data.pfun
import logic.relation
import data.fun_like.basic
import computability.turing_machine

open relation (refl_trans_gen)

@[ext]
structure execution (σ : Type*) :=
(next : σ →. option σ)
(start : σ)

namespace execution
variables {σ τ : Type*}

def states (f : execution σ) : set σ :=
{s | refl_trans_gen (λ x y, some y ∈ f.next x) f.start s}

lemma start_mem_states (f : execution σ) : f.start ∈ f.states :=
relation.refl_trans_gen.refl

lemma mem_states_of_fwd {f : execution σ} {x y} (hx : x ∈ f.states) (hxy : some y ∈ f.next x) :
  y ∈ f.states :=
relation.refl_trans_gen.tail hx hxy

lemma fwd_states {f : execution σ} {y} (hy : some y ∈ f.next f.start) :
  f.states = insert f.start (states ⟨f.next, y⟩) :=
begin
  ext, dsimp [states],
  rw relation.refl_trans_gen.cases_head_iff, rw ← part.eq_some_iff at hy,
  simp [hy], tauto,
end

@[elab_as_eliminator]
theorem step_induction {P : σ → Prop} {f : execution σ} {x : σ} (hx : x ∈ f.states) (base : P f.start)
  (step : ∀ ⦃x y⦄, x ∈ f.states → P x → some y ∈ f.next x → P y) : P x :=
by { induction hx with _ _ H h ih, { assumption, }, { refine step H ih h, } }

lemma mem_ran_of_mem_states {f : execution σ} {y : σ} (hy : y ∈ f.states) :
  y = f.start ∨ some y ∈ f.next.ran :=
begin
  apply step_induction hy, { exact or.inl rfl, },
  intros x y hx _,
  simp [pfun.ran], tauto, 
end


variables (f : execution σ)

def eval : part σ :=
pfun.fix (λ s, (f.next s).map (λ x, x.elim (sum.inl s) sum.inr)) f.start

theorem eval_from {f : execution σ} {x : σ} (hx : x ∈ f.states) : eval ⟨f.next, x⟩ = f.eval :=
begin
  apply execution.step_induction hx, { refl, },
  intros x y _ h hn,
  rw [eval, pfun.fix_fwd x y] at h, { exact h, },
  simp, use some y, simpa
end

@[elab_as_eliminator] def eval_induction {σ}
  {f : σ →. option σ} {b : σ} {C : σ → Sort*} {a : σ} (h : b ∈ eval ⟨f, a⟩)
  (H : ∀ a, b ∈ eval ⟨f, a⟩ →
    (∀ a', (some a') ∈ f a → C a') → C a) : C a :=
by { dsimp only [eval] at h, exact pfun.fix_induction h (λ _ b ih, H _ b (λ _ ha, ih _ (by { rw ← part.eq_some_iff at ha, simp [ha], }))), }

theorem mem_eval {σ} {f : execution σ} {b} :
  b ∈ f.eval ↔ b ∈ f.states ∧ none ∈ f.next b :=
begin
  split,
  { intro h, cases f with f a, dsimp only at *,
    apply eval_induction h, clear h a, intros a hb ih,
    have : (f a).dom := by simpa using pfun.dom_of_mem_fix hb, 
    rw part.dom_iff_mem at this,
    rcases this with ⟨a'|a', ha'⟩, rw ← part.eq_some_iff at ha',
    { rw [eval] at hb, cases (part.mem_unique hb (pfun.fix_stop a _) : b = a),
      { rw part.eq_some_iff at ha', exact ⟨start_mem_states _, ha'⟩, }, { simp [ha'], } },
    specialize ih a' ha',
    refine ⟨_, ih.2⟩, rw @fwd_states _ ⟨f, a⟩ _ ha', simp, right, exact ih.1, },
  { rintro ⟨h₁, h₂⟩,
    rw ← eval_from h₁, dsimp only [eval] at *, 
    apply pfun.fix_stop, 
    rw ← part.eq_some_iff at h₂, simp [h₂], }
end

end execution

section tr_step
variables {σ τ : Type*}

structure stepwise_tr (f : execution σ) (g : execution τ) :=
(rel : σ → τ → Prop)
(dom_iff : ∀ {x y}, x ∈ f.states → y ∈ g.states → rel x y → ((f.next x).dom ↔ (g.next y).dom))
(some_iff : ∀ {x y x' y'}, x ∈ f.states → y ∈ g.states → rel x y → some x' ∈ f.next x → some y' ∈ g.next y → rel x' y')
(none_iff : ∀ {x y}, x ∈ f.states → y ∈ g.states → rel x y → (none ∈ f.next x ↔ none ∈ g.next y))
(start : rel f.start g.start)

infixr ` ∼ₛ `:25 := stepwise_tr


namespace stepwise_tr
variables {f : execution σ} {g : execution τ} (h : f ∼ₛ g)

@[symm, simps]
def symm : g ∼ₛ f :=
{ rel := λ a b, h.rel b a,
  dom_iff := λ x y hx hy hrel, by rw h.dom_iff hy hx hrel,
  some_iff := λ x y x' y' hx hy hrel h₁ h₂, h.some_iff hy hx hrel h₂ h₁,
  none_iff := λ x y hx hy hrel, by rw h.none_iff hy hx hrel,
  start := h.start }

theorem exists_some_of {x y x'} (hx : x ∈ f.states) (hy : y ∈ g.states) (hrel : h.rel x y)
  (hx' : some x' ∈ f.next x) : ∃ y', some y' ∈ g.next y ∧ h.rel x' y' :=
begin
  obtain ⟨y', hy'⟩ : ∃ y', y' ∈ g.next y,
  { rw [← part.dom_iff_mem, ← h.dom_iff hx hy hrel, part.dom_iff_mem], exact ⟨_, hx'⟩, },
  cases y', { rw ← h.none_iff hx hy hrel at hy', cases part.mem_unique hx' hy', },
  refine ⟨_, hy', _⟩,
  exact h.some_iff hx hy hrel hx' hy',
end

theorem exists_some_iff {x y} (hx : x ∈ f.states) (hy : y ∈ g.states) (hrel : h.rel x y) :
  (∃ x', some x' ∈ f.next x) ↔ (∃ y', some y' ∈ g.next y) :=
by { split, { rintro ⟨x', hx'⟩, rcases h.exists_some_of hx hy hrel hx' with ⟨y', hy', _⟩, exact ⟨y', hy'⟩, },
    { rintro ⟨y', hy'⟩, rcases h.symm.exists_some_of hy hx hrel hy' with ⟨x', hx', _⟩, exact ⟨x', hx'⟩, }, }

@[trans, simps]
def trans {γ : Type*} {f : execution σ} {g : execution τ} {h : execution γ}
  (r₁ : f ∼ₛ g) (r₂ : g ∼ₛ h) : f ∼ₛ h :=
{ rel := λ a b, ∃ c ∈ g.states, r₁.rel a c ∧ r₂.rel c b,
  dom_iff := λ x y hx hy ⟨c, hc, h₁, h₂⟩, by rw [r₁.dom_iff hx hc h₁, r₂.dom_iff hc hy h₂],
  some_iff := λ x y x' y' hx hy ⟨c, hc, hc₁, hc₂⟩ h₁ h₂,
begin
  obtain ⟨c', h₁c', h₂c'⟩ := r₁.exists_some_of hx hc hc₁ h₁,
  refine ⟨_, execution.mem_states_of_fwd hc h₁c', h₂c', _⟩,
  exact r₂.some_iff hc hy hc₂ h₁c' h₂,
end,
  none_iff := λ x y hx hy ⟨c, hc, h₁, h₂⟩, by rw [r₁.none_iff hx hc h₁, r₂.none_iff hc hy h₂],
  start := ⟨g.start, execution.start_mem_states _, r₁.start, r₂.start⟩, }

@[simps]
def extend (r₁ : f ∼ₛ g) (rel₂ : σ → τ → Prop)
  (some_iff : ∀ {x y x' y'}, x ∈ f.states → y ∈ g.states → r₁.rel x y → rel₂ x y → some x' ∈ f.next x → some y' ∈ g.next y → rel₂ x' y')
  (start : rel₂ f.start g.start) : f ∼ₛ g :=
{ rel := λ a b, r₁.rel a b ∧ rel₂ a b,
  dom_iff := λ x y hx hy hrel, by rw r₁.dom_iff hx hy hrel.1,
  some_iff := λ x y x' y' hx hy hrel hx' hy', ⟨r₁.some_iff hx hy hrel.1 hx' hy', some_iff hx hy hrel.1 hrel.2 hx' hy'⟩,
  none_iff := λ x y hx hy hrel, by rw r₁.none_iff hx hy hrel.1,
  start := ⟨r₁.start, start⟩ }

theorem exists_state_of {x} (hx : x ∈ f.states) : ∃ y, y ∈ g.states ∧ h.rel x y :=
begin
  apply execution.step_induction hx; clear hx x,
  { exact ⟨_, g.start_mem_states, h.start⟩, },
  rintros x x' hx ⟨y, h₁y, h₂y⟩ hx',
  obtain ⟨y', hy', H⟩ := h.exists_some_of hx h₁y h₂y hx',
  exact ⟨y', execution.mem_states_of_fwd h₁y hy', H⟩,
end

theorem mem_eval_of {x} (hx : x ∈ f.eval) : ∃ y, y ∈ g.eval ∧ h.rel x y :=
begin
  simp only [execution.mem_eval] at *, cases hx with hx₁ hx₂,
  obtain ⟨y, hy, H⟩ := h.exists_state_of hx₁, refine ⟨y, ⟨hy, _⟩, H⟩,
  rwa ← h.none_iff hx₁ hy H,
end

theorem rel_of_mem_eval {x y} (hx : x ∈ f.eval) (hy : y ∈ g.eval) : h.rel x y :=
begin
  obtain ⟨y, hy', hrel⟩ := h.mem_eval_of hx,
  cases part.mem_unique hy hy',
  exact hrel,
end

theorem eval_dom_iff (h : f ∼ₛ g) : f.eval.dom ↔ g.eval.dom :=
begin
  simp only [part.dom_iff_mem], split,
  { rintro ⟨x, hx⟩, obtain ⟨y, hy, _⟩ := h.mem_eval_of hx, exact ⟨y, hy⟩, },
  { rintro ⟨y, hy⟩, obtain ⟨x, hx, _⟩ := h.symm.mem_eval_of hy, exact ⟨x, hx⟩, },
end

end stepwise_tr

section track_with
variables (f : execution σ) (state : τ → σ →. τ) (s : τ)
def execution.track_with : execution (τ × σ) :=
{ next := λ x, (f.next x.2).bind (λ x', x'.elim (part.some none) (λ x'', (state x.1 x.2).map (λ s', some (s', x'')))),
-- { next := λ x, (state x.1 x.2).bind $ λ s', (f.next x.2).map $ λ x', x'.map (prod.mk s'),
  start := (s, f.start) }

lemma _root_.option.elim_comp {α β} (P : β → Sort*) (x : option α) (y : β) (f : α → β)  :
  P (x.elim y f) = (x.elim (P y) (P ∘ f)) :=
by cases x; simp

@[simp] lemma _root_.option.elim_true {α} (x : option α) (f : α → Prop) :
  x.elim true f ↔ ∀ y, x = some y → f y :=
by cases x; simp

@[simp] lemma _root_.option.eq_none_iff_forall_not_some {α} (x : option α) :
  (∀ y, x ≠ some y) ↔ (x = none) :=
by simp_rw [ne.def, ← not_exists, ← option.is_some_iff_exists, option.not_is_some_iff_eq_none]

@[simp] lemma _root_.option.elim_false {α} (x : option α) (f : α → Prop) :
  x.elim false f ↔ (∃ y, x = some y ∧ f y) :=
by cases x; simp

@[simp] lemma execution.track_with_dom_iff {x : τ × σ} :
  ((f.track_with state s).next x).dom ↔ (f.next x.2).dom ∧ (∀ y, some y ∈ f.next x.2 → (state x.1 x.2).dom) :=
by simp [execution.track_with, option.elim_comp part.dom, function.comp, part.get_eq_iff_mem]

@[simp] lemma execution.track_with_some_def {x y : τ × σ} :
  some y ∈ (f.track_with state s).next x ↔ y.1 ∈ state x.1 x.2 ∧ some y.2 ∈ f.next x.2 :=
begin
  cases x with x₁ x₂, cases y with y₁ y₂,
  simp [execution.track_with, option.elim_comp (has_mem.mem (some (y₁, y₂)))], tidy,
end

@[simp] lemma execution.track_with_none_def {x : τ × σ} :
  none ∈ (f.track_with state s).next x ↔ none ∈ f.next x.2 :=
by simp [execution.track_with, option.elim_comp (has_mem.mem none), imp_false]

@[simp] lemma execution.track_with_start :
  (f.track_with state s).start = (s, f.start) := rfl

@[simps]
def tr_of_track_with (hd : ∀ {x x'} (y), x ∈ f.states → some x' ∈ f.next x → (state y x).dom) :
  f ∼ₛ f.track_with state s :=
{ rel := λ a b, a = b.snd,
  dom_iff := λ x y hx hy, by { rintro rfl, simp, tauto, },
  some_iff := λ x y x' y' _ _,
begin
  rintro rfl,
  intros h, rw ← part.eq_some_iff at h,
  cases y', simp [h], tauto,
end,
  none_iff := λ x y hx _,
begin
  cases y with y₁ y₂,
  rintro rfl,
  simp,
end,
  start := rfl }

@[simp] lemma track_with_eval_dom (hd : ∀ ⦃x x'⦄ (y), x ∈ f.states → some x' ∈ f.next x → (state y x).dom) :
  (f.track_with state s).eval.dom ↔ f.eval.dom :=
(tr_of_track_with f state s hd).eval_dom_iff.symm 

lemma track_with_change_start (s' : τ × σ) :
  (execution.mk (f.track_with state s).next s') = (execution.mk f.next s'.2).track_with state s'.1 :=
by { ext : 1, { simp [execution.track_with], }, { simp, } }

section time_with

def execution.time_with (time : σ →. ℕ) : execution (ℕ × σ) :=
f.track_with (λ n s, (time s).map (+n)) 0

@[simp] lemma execution.none_mem_time_with (time : σ →. ℕ) {x : ℕ × σ} :
  none ∈ (f.time_with time).next x ↔ none ∈ f.next x.2 :=
by simp [execution.time_with] 

@[simps]
def execution.time_with_tr (time : σ →. ℕ) (hd : ∀ {x x'}, x ∈ f.states → some x' ∈ f.next x → (time x).dom) :
  f ∼ₛ f.time_with time :=
tr_of_track_with f _ _ (λ x y hx, by simpa using hd)

def execution.time (time : σ →. ℕ) : part ℕ :=
(f.time_with time).eval.map prod.fst

@[simp] lemma _root_.pfun.pure_dom_eq {α β} (x : β) :
  (pfun.pure x : α →. β).dom = set.univ := rfl
@[simp] lemma _root_.pfun.pure_dom {α β} (x : β) (y : α) :
  (pfun.pure x y).dom := trivial
@[simp] lemma _root_.pfun.pure_apply {α β} (x : β) (y : α) :
  (pfun.pure x y) = part.some x := rfl

@[simps]
def execution.time_with_bound (J : ℕ) (time : σ →. ℕ) (hd : ∀ ⦃x x'⦄, x ∈ f.states → some x' ∈ f.next x → (time x).dom)
  (hJ : ∀ ⦃x t⦄, x ∈ f.states → t ∈ time x → t ≤ J) :
  f.time_with time ∼ₛ f.time_with (pfun.pure 1) :=
((f.time_with_tr time hd).symm.trans (f.time_with_tr _ (by simp))).extend (λ s₁ s₂, s₁.1 ≤ J * s₂.1) 
  (λ x y x' y' hx hy hr₁ hr₂, 
begin
  cases x with xt x, cases y with yt y, cases x' with x't x', cases y' with y't y', dsimp only at *,
  simp at hr₁, rcases hr₁ with ⟨hr₁, rfl⟩,
  simp [execution.time_with],
  rintros t ht rfl hx'' rfl hy'',
  specialize hJ hr₁ ht, rw mul_add, mono, simpa using hJ,
end)
  (by simp [execution.time_with])

@[simps]
def stepwise_tr.time_with_pure_tr_aux {f : execution σ} {g : execution τ} (h : f ∼ₛ g) :
  f.time_with (pfun.pure 1) ∼ₛ g.time_with (pfun.pure 1) :=
((f.time_with_tr (pfun.pure 1) (by simp)).symm.trans h).trans (g.time_with_tr (pfun.pure 1) (by simp))

def stepwise_tr.time_with_pure_tr {f : execution σ} {g : execution τ} (h : f ∼ₛ g) :
  f.time_with (pfun.pure 1) ∼ₛ g.time_with (pfun.pure 1) :=
h.time_with_pure_tr_aux.extend (λ n₁ n₂, n₁.1 = n₂.1) 
(by { rintros ⟨t₀, x₀⟩ ⟨t₀', y₀⟩ ⟨t₁, x₁⟩ ⟨t₁', y₁⟩, simp [execution.time_with], intros, subst_vars, })
rfl

@[simp] lemma stepwise_tr.time_with_pure_tr_rel {f : execution σ} {g : execution τ} {h : f ∼ₛ g} {s₀ : ℕ × σ} {s₁ : ℕ × τ} :
  h.time_with_pure_tr.rel s₀ s₁ ↔ s₀.1 = s₁.1 ∧ h.rel s₀.2 s₁.2 ∧ s₀.2 ∈ f.states ∧ s₁.2 ∈ g.states :=
by { simp [stepwise_tr.time_with_pure_tr], tidy, }

private lemma stepwise_tr.time_pure_eq_aux {f : execution σ} {g : execution τ} (h : f ∼ₛ g) {T}
  (hT : T ∈ f.time (pfun.pure 1)) : T ∈ g.time (pfun.pure 1) :=
begin
  simp [execution.time] at hT ⊢,
  rcases hT with ⟨x, hx⟩,
  obtain ⟨⟨t', y⟩, h₁, h₂⟩ := h.time_with_pure_tr.mem_eval_of hx,
  use y, simp at h₂, rwa h₂.1,
end

lemma stepwise_tr.time_pure_eq {f : execution σ} {g : execution τ} (h : f ∼ₛ g) :
  f.time (pfun.pure 1) = g.time (pfun.pure 1) :=
by { ext T, split, { exact stepwise_tr.time_pure_eq_aux h, }, { exact stepwise_tr.time_pure_eq_aux h.symm, } }

theorem execution.time_le (J : ℕ) (time : σ →. ℕ) (hd : ∀ ⦃x y⦄, x ∈ f.states → some y ∈ f.next x → (time x).dom)
  (hJ : ∀ ⦃x t⦄, x ∈ f.states → t ∈ time x → t ≤ J) {N} (hN : N ∈ f.time (pfun.pure 1)) :
  ∃ t, t ∈ f.time time ∧ t ≤ J * N :=
begin
  let R := f.time_with_bound J time hd hJ,
  simp [execution.time] at hN ⊢, cases hN with x₂ ht₂,
  have := R.symm.mem_eval_of ht₂, simp at this,
  rcases this with ⟨t, x, ht, _, H⟩,
  exact ⟨t, ⟨x, ht⟩, H⟩,
end

@[simps]
def execution.time_tr_self (time : σ →. ℕ) (t₀ : ℕ) :
  f.time_with time ∼ₛ (f.track_with (λ n s, (time s).map (+n)) t₀) :=
{ rel := λ a b, b.1 = a.1 + t₀ ∧ b.2 = a.2,
  dom_iff := λ x y hx hy, by { cases x, cases y, dsimp only, rintros ⟨rfl, rfl⟩, simp [execution.time_with], },
  some_iff := λ x y x' y' hx hy, 
begin
  cases x, cases y, cases x', cases y', dsimp only,
  rintros ⟨rfl, rfl⟩, simp [execution.time_with],
  rintros _ h₀ rfl h₁ _ h₂ rfl h₃,
  cases part.mem_unique h₀ h₂, cases part.mem_unique h₁ h₃, simp [add_assoc],
end,
  none_iff := λ x y hx hy, by { cases x, cases y, dsimp only, rintros ⟨rfl, rfl⟩, simp [execution.time_with], },
  start := by simp [execution.time_with] }

theorem execution.time_fwd (time : σ →. ℕ)  (t₀ : ℕ) :
  (f.track_with (λ n s, (time s).map (+n)) t₀).eval = (f.time_with time).eval.map (prod.map (+t₀) id) :=
begin
  let R := (f.time_tr_self time t₀), apply part.ext',
  { rw R.symm.eval_dom_iff, simp, },
  intros h₁ h₂, rw part.dom_iff_mem at h₁ h₂, rcases h₁ with ⟨⟨t₁, s₁⟩, h₁⟩, rcases h₂ with ⟨⟨t₂, s₂⟩, h₂⟩, rw [part.get_eq_of_mem h₁, part.get_eq_of_mem h₂],
  simp at h₂, rcases h₂ with ⟨t₂, h₂, rfl⟩,
  have := R.rel_of_mem_eval h₂ h₁, simpa,
end

theorem execution.start_time_le_time (time : σ →. ℕ) {t₀ N : ℕ} (hN : ∃ xf : σ, (N, xf) ∈ (f.track_with (λ n s, (time s).map (+n)) t₀).eval) :
  t₀ ≤ N :=
begin
  simp_rw execution.mem_eval at hN, rcases hN with ⟨xf, H, _⟩,
  apply @execution.step_induction _ (λ S : ℕ × σ, t₀ ≤ S.1) _ _ H,
  { simp, }, { rintros ⟨_, _⟩ ⟨_, _⟩ _ h, simp, rintros _ _ rfl _, refine h.trans _, simp, }
end

theorem execution.state_time_le_time (time : σ →. ℕ) {N} (hN : N ∈ f.time time) {s : ℕ × σ} (hs : s ∈ (f.time_with time).states) :
  s.1 ≤ N :=
begin
  simp [execution.time, ← execution.eval_from hs] at hN,
  simp [execution.time_with, track_with_change_start] at hN, 
  exact execution.start_time_le_time _ time hN,
end

end time_with

end track_with

end tr_step

