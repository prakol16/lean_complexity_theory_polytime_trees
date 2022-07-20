import data.pfun
import logic.relation
import logic.function.iterate
import tactic.apply_fun

namespace option

@[simp] lemma map_eq_some'_symm {α β : Type*} (f : α → β) (x : option α) (y : β) :
  some y = x.map f ↔ ∃ a, x = some a ∧ f a = y := by { cases x; simp, exact comm, }

@[simp] lemma map_eq_none'_symm {α β : Type*} (f : α → β) (x : option α) :
  none = x.map f ↔ none = x := by cases x; simp

end option

namespace pfun

/-- Restrict with the intersection of a set -/
def res_inter {α β : Type*} (f : α →. β) (p : set α) : α →. β :=
f.restrict (set.inter_subset_right p f.dom)

@[simp] lemma mem_res_inter {α β : Type*} {f : α →. β} {p : set α} {x y} :
  y ∈ f.res_inter p x ↔ x ∈ p ∧ y ∈ f x :=
by { simp [res_inter], tauto, }

end pfun

open relation
open nat (iterate)
open function (update iterate_succ iterate_succ_apply iterate_succ'
  iterate_succ_apply' iterate_zero_apply)

namespace part_eval

/-- Run a state transition function `σ → option σ` "to completion". The return value is the last
state returned before a `none` result. If the state transition function always returns `some` or any step of the
transition function diverges, then the computation diverges, returning `part.none`. -/
def eval {σ} (f : σ →. option σ) : σ → part σ :=
pfun.fix (λ s, (f s).map (λ x, x.elim (sum.inl s) sum.inr))

/-- The reflexive transitive closure of a state transition function. `reaches f a b` means
there is a finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`.
This relation permits zero steps of the state transition function. -/
def reaches {σ} (f : σ →. option σ) : σ → σ → Prop :=
refl_trans_gen (λ a b, some b ∈ f a)

@[refl] lemma reaches.refl {σ} (f : σ →. option σ) (x : σ) :
  reaches f x x := refl_trans_gen.refl

@[trans] lemma reaches.trans {σ} {f : σ →. option σ} {x y z : σ} :
  reaches f x y → reaches f y z → reaches f x z := refl_trans_gen.trans

lemma reaches_fwd {σ} {f : σ →. option σ} {x y : σ} :
  some y ∈ f x → reaches f x y := @refl_trans_gen.single _ _ x y

theorem reaches_mono {σ} {f : σ →. option σ} (S : set σ) (hS : S ⊆ f.dom) {x y} (hf : reaches (f.restrict hS) x y) :
  reaches f x y :=
by { apply refl_trans_gen.mono _ hf, simp, }

theorem invariant_of_reaches {σ} {f : σ →. option σ} (S : set σ) (hS : ∀ ⦃x y⦄, x ∈ S → some y ∈ f x → y ∈ S)
  {x y} (hx : x ∈ S) (hf : reaches f x y) : y ∈ S :=
by { induction hf with x' y' hfx' hfy' ih, { exact hx, }, exact hS ih hfy', }

theorem reaches_of_invariant {σ} {f : σ →. option σ} (S : set σ) (hS : ∀ ⦃x y⦄, x ∈ S → some y ∈ f x → y ∈ S)
  {x y} (hx : x ∈ S) (hf : reaches f x y) : reaches (f.res_inter S) x y :=
begin
  induction hf using relation.refl_trans_gen.head_induction_on with x' y' hx' hy' ih, { refl, },
  apply reaches.trans (reaches_fwd _) (ih _),
  { simp only [pfun.mem_res_inter], exact ⟨hx, hx'⟩, }, { exact hS hx hx', }
end

/-- The transitive closure of a state transition function. `reaches₁ f a b` means there is a
nonempty finite sequence of steps `f a = some a₁`, `f a₁ = some a₂`, ... such that `aₙ = b`.
This relation does not permit zero steps of the state transition function. -/
def reaches₁ {σ} (f : σ →. option σ) : σ → σ → Prop :=
trans_gen (λ a b, some b ∈ f a)

theorem reaches_iff_eq_or_reaches₁ {σ} {f : σ →. option σ} {a b} :
  reaches f a b ↔ b = a ∨ reaches₁ f a b := refl_trans_gen_iff_eq_or_trans_gen

theorem reaches₁_head'_iff {σ} {f : σ →. option σ} {a b} :
  reaches₁ f a b ↔ ∃ c : σ, some c ∈ f a ∧ reaches f c b := trans_gen.head'_iff

theorem reaches₁_eq {σ} {f : σ →. option σ} {a b c}
  (h : f a = f b) : reaches₁ f a c ↔ reaches₁ f b c :=
trans_gen.head'_iff.trans (trans_gen.head'_iff.trans $ by rw h).symm

theorem reaches_total {σ} {f : σ →. option σ}
  {a b c} (hab : reaches f a b) (hac : reaches f a c) :
  reaches f b c ∨ reaches f c b :=
refl_trans_gen.total_of_right_unique (λ x y z hx hy, option.some_injective _ (part.mem_unique hx hy)) hab hac

theorem reaches₁_fwd {σ} {f : σ →. option σ}
  {a b c} (h₁ : reaches₁ f a c) (h₂ : some b ∈ f a) : reaches f b c :=
begin
  rw reaches₁_head'_iff at h₁, rcases h₁ with ⟨b', ⟨h₂', H⟩⟩,
  cases part.mem_unique h₂ h₂', exact H,
end

theorem reaches₁_single {σ} {f : σ →. option σ}
  {a b} : some b ∈ f a → reaches₁ f a b :=
@trans_gen.single σ _ a b

/-- A variation on `reaches`. `reaches₀ f a b` holds if whenever `reaches₁ f b c` then
`reaches₁ f a c`. This is a weaker property than `reaches` and is useful for replacing states with
equivalent states without taking a step. -/
def reaches₀ {σ} (f : σ →. option σ) (a b : σ) : Prop :=
∀ c, reaches₁ f b c → reaches₁ f a c

theorem reaches₀.trans {σ} {f : σ →. option σ} {a b c : σ}
  (h₁ : reaches₀ f a b) (h₂ : reaches₀ f b c) : reaches₀ f a c
| d h₃ := h₁ _ (h₂ _ h₃)

@[refl] theorem reaches₀.refl {σ} {f : σ →. option σ} (a : σ) : reaches₀ f a a
| b h := h

theorem reaches₀.single {σ} {f : σ →. option σ} {a b : σ}
  (h : some b ∈ f a) : reaches₀ f a b
| c h₂ := h₂.head h

theorem reaches₀.head {σ} {f : σ →. option σ} {a b c : σ}
  (h : some b ∈ f a) (h₂ : reaches₀ f b c) : reaches₀ f a c :=
(reaches₀.single h).trans h₂

theorem reaches₀.tail {σ} {f : σ →. option σ} {a b c : σ}
  (h₁ : reaches₀ f a b) (h : some c ∈ f b) : reaches₀ f a c :=
h₁.trans (reaches₀.single h)

theorem reaches₀_eq {σ} {f : σ →. option σ} {a b}
  (e : f a = f b) : reaches₀ f a b
| d h := (reaches₁_eq e).2 h

theorem reaches₁.to₀ {σ} {f : σ →. option σ} {a b : σ}
  (h : reaches₁ f a b) : reaches₀ f a b
| c h₂ := h.trans h₂

theorem reaches.to₀ {σ} {f : σ →. option σ} {a b : σ}
  (h : reaches f a b) : reaches₀ f a b
| c h₂ := h₂.trans_right h

theorem reaches₀.tail' {σ} {f : σ →. option σ} {a b c : σ}
  (h : reaches₀ f a b) (h₂ : some c ∈ f b) : reaches₁ f a c :=
h _ (trans_gen.single h₂)

/-- (co-)Induction principle for `eval`. If a property `C` holds of any point `a` evaluating to `b`
which is either terminal (meaning `a = b`) or where the next point also satisfies `C`, then it
holds of any point where `eval f a` evaluates to `b`. This formalizes the notion that if
`eval f a` evaluates to `b` then it reaches terminal state `b` in finitely many steps. -/
@[elab_as_eliminator] def eval_induction {σ}
  {f : σ →. option σ} {b : σ} {C : σ → Sort*} {a : σ} (h : b ∈ eval f a)
  (H : ∀ a, b ∈ eval f a →
    (∀ a', f a = part.some (some a') → C a') → C a) : C a :=
pfun.fix_induction h (λ _ b ih, H _ b (λ _ ha, ih _ (by simp [ha])))

theorem mem_eval {σ} {f : σ →. option σ} {a b} :
  b ∈ eval f a ↔ reaches f a b ∧ f b = part.some none :=
begin
  split,
  { intro h, 
    apply eval_induction h, clear h a, intros a hb ih,
    have : (f a).dom := by simpa using pfun.dom_of_mem_fix hb, 
    rw part.dom_iff_mem at this,
    rcases this with ⟨a'|a', ha'⟩, rw ← part.eq_some_iff at ha',
    { rw [eval] at hb, cases (part.mem_unique hb (pfun.fix_stop a _) : b = a),
      { exact ⟨by refl, ha'⟩, }, { simp [ha'], } },
    specialize ih a' (by rwa part.eq_some_iff),
    exact ⟨(reaches_fwd ha').trans ih.1, ih.2⟩, },
  { rintro ⟨h₁, h₂⟩,
    induction h₁ using relation.refl_trans_gen.head_induction_on with a' b' ha' hb ih,
    { apply pfun.fix_stop, simp [h₂], },
    rw [eval, pfun.fix_fwd _ b'], { exact ih, },
    rw ← part.eq_some_iff at ha', simp [ha'], }
end

@[simp] lemma eval_next_iter_eq_none {σ} (f : σ →. option σ) (a : σ) (h : (eval f a).dom) :
  f ((eval f a).get h) = part.some none :=
by { have := part.get_mem h, rw mem_eval at this, exact this.2, }

theorem eval_maximal₁ {σ} {f : σ →. option σ} {a b : σ}
  (h : b ∈ eval f a) (c) : ¬ reaches₁ f b c | bc :=
let ⟨ab, b0⟩ := mem_eval.1 h, ⟨b', h', _⟩ := trans_gen.head'_iff.1 bc in
by { rw b0 at h', simpa using h', }

theorem eval_maximal {σ} {f : σ →. option σ} {a b}
  (h : b ∈ eval f a) {c} : reaches f b c ↔ c = b :=
let ⟨ab, b0⟩ := mem_eval.1 h in
refl_trans_gen_iff_eq $ λ b' h',
by { rw b0 at h', simpa using h', }

theorem reaches_eval {σ} {f : σ →. option σ} {a b}
  (ab : reaches f a b) : eval f a = eval f b :=
part.ext $ λ c,
 ⟨λ h, let ⟨ac, c0⟩ := mem_eval.1 h in
    mem_eval.2 ⟨(or_iff_left_of_imp $ by exact
      λ cb, (eval_maximal h).1 cb ▸ refl_trans_gen.refl).1
      (reaches_total ab ac), c0⟩,
  λ h, let ⟨bc, c0⟩ := mem_eval.1 h in mem_eval.2 ⟨ab.trans bc, c0⟩,⟩

/-- Given a relation `tr : σ₁ → σ₂ → Prop` between state spaces, and state transition functions
`f₁ : σ₁ → option σ₁` and `f₂ : σ₂ → option σ₂`, `respects f₁ f₂ tr` means that if `tr a₁ a₂` holds
initially and `f₁` takes a step to `a₂` then `f₂` will take one or more steps before reaching a
state `b₂` satisfying `tr a₂ b₂`, and if `f₁ a₁` terminates then `f₂ a₂` also terminates.
Such a relation `tr` is also known as a refinement. -/
-- def respects {σ₁ σ₂}
--   (f₁ : σ₁ →. option σ₁) (f₂ : σ₂ →. option σ₂) (tr : σ₁ → σ₂ → Prop) :=
-- ∀ ⦃a₁ a₂⦄, tr a₁ a₂ → (match f₁ a₁ with
--   | part.none := f₂ a₂ = part.none 
--   | part.some (some b₁) := ∃ b₂, tr b₁ b₂ ∧ reaches₁ f₂ a₂ b₂
--   | part.some none := f₂ a₂ = none
--   end : Prop)

structure respects {σ₁ σ₂} (f₁ : σ₁ →. option σ₁) (f₂ : σ₂ →. option σ₂) (tr : σ₁ → σ₂ → Prop) : Prop :=
(dom_of_dom : ∀ ⦃a₁ a₂⦄, tr a₁ a₂ → (f₂ a₂).dom → (f₁ a₁).dom)
(some_of_some : ∀ ⦃a₁ a₂ b₁⦄, tr a₁ a₂ → some b₁ ∈ (f₁ a₁) → ∃ b₂, tr b₁ b₂ ∧ reaches₁ f₂ a₂ b₂)
(none_of_none : ∀ ⦃a₁ a₂⦄, tr a₁ a₂ → none ∈ (f₁ a₁) → none ∈ (f₂ a₂))

variables {σ₁ σ₂ : Type*} {f₁ : σ₁ →. option σ₁} {f₂ : σ₂ →. option σ₂} {tr : σ₁ → σ₂ → Prop}

lemma respects.exists_some {a₁ a₂ b₁} (H : respects f₁ f₂ tr) (aa : tr a₁ a₂) (hb₁ : some b₁ ∈ f₁ a₁) :
  ∃ b₂, some b₂ ∈ f₂ a₂ :=
by { obtain ⟨b₂, ⟨_, hb₂⟩⟩ := H.some_of_some aa hb₁, rw reaches₁_head'_iff at hb₂, tauto, }

lemma respects.dom_iff_domm {a₁ a₂} (H : respects f₁ f₂ tr) (aa : tr a₁ a₂) :
  (f₁ a₁).dom ↔ (f₂ a₂).dom :=
begin
  refine ⟨λ h, _, H.dom_of_dom aa⟩,
  rw [part.dom_iff_mem] at h ⊢, cases h with b₁ hb,
  cases b₁,
  { use none, exact H.none_of_none aa hb, },
  { obtain ⟨b₂, hb₂⟩ := H.exists_some aa hb, exact ⟨_, hb₂⟩, }
end

lemma respects.none_iff_none {a₁ a₂} (H : respects f₁ f₂ tr) (aa : tr a₁ a₂) :
  none ∈ f₁ a₁ ↔ none ∈ f₂ a₂ :=
begin
  refine ⟨H.none_of_none aa, λ h, _⟩,
  obtain ⟨x, hx⟩ : ∃ x, x ∈ f₁ a₁, { rw [← part.dom_iff_mem, H.dom_iff_domm aa, part.dom_iff_mem], exact ⟨_, h⟩, },
  cases x, { exact hx, },
  obtain ⟨_, hb⟩ := H.exists_some aa hx, cases part.mem_unique h hb,
end

lemma respects.some_iff_some {a₁ a₂} (H : respects f₁ f₂ tr) (aa : tr a₁ a₂) :
  (∃ b₁, some b₁ ∈ f₁ a₁) ↔ (∃ b₂, some b₂ ∈ f₂ a₂) :=
begin
  refine ⟨λ ⟨b₁, hb₁⟩, H.exists_some aa hb₁, _⟩,
  rintro ⟨b₂, hb₂⟩,
  obtain ⟨x, hx⟩ : ∃ x, x ∈ f₁ a₁, { rw [← part.dom_iff_mem, H.dom_iff_domm aa, part.dom_iff_mem], exact ⟨_, hb₂⟩, },
  cases x, { rw H.none_iff_none aa at hx, cases part.mem_unique hb₂ hx, },
  exact ⟨_, hx⟩,
end 

theorem tr_reaches₁
  (H : respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) {b₁} (ab : reaches₁ f₁ a₁ b₁) :
  ∃ b₂, tr b₁ b₂ ∧ reaches₁ f₂ a₂ b₂ :=
begin
  induction ab with c₁ ac c₁ d₁ ac cd IH,
  { exact H.some_of_some aa ac, },
  { rcases IH with ⟨c₂, cc, ac₂⟩,
    obtain ⟨b₂, ⟨h₁, h₂⟩⟩ := H.some_of_some cc cd,
    exact ⟨b₂, ⟨h₁, ac₂.trans h₂⟩⟩, }
end

theorem tr_reaches {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) {b₁} (ab : reaches f₁ a₁ b₁) :
  ∃ b₂, tr b₁ b₂ ∧ reaches f₂ a₂ b₂ :=
begin
  rcases refl_trans_gen_iff_eq_or_trans_gen.1 ab with rfl | ab,
  { exact ⟨_, aa, refl_trans_gen.refl⟩ },
  { exact let ⟨b₂, bb, h⟩ := tr_reaches₁ H aa ab in
    ⟨b₂, bb, h.to_refl⟩ }
end

theorem tr_reaches_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) {b₂} (ab : reaches f₂ a₂ b₂) :
  ∃ c₁ c₂, reaches f₂ b₂ c₂ ∧ tr c₁ c₂ ∧ reaches f₁ a₁ c₁ :=
begin
  induction ab with a₂' a₂'' ha₂ ha₂' ih,
  { refine ⟨a₁, a₂, _, aa, _⟩; refl, },
  rcases ih with ⟨c₁, c₂, c₂h, trh, c₁h⟩,
  by_cases H : c₂ = a₂',
  { subst H, clear c₂h,
    obtain ⟨c₁', hc₁'⟩ := (H.some_iff_some trh).mpr ⟨_, ha₂'⟩,
    obtain ⟨c₂', hc₂, hc₂'⟩ := H.some_of_some trh hc₁', 
    exact ⟨c₁', c₂', reaches₁_fwd hc₂' ha₂', hc₂, c₁h.trans (reaches_fwd hc₁')⟩, },
  refine ⟨c₁, c₂, _, trh, c₁h⟩,
  simp_rw [reaches_iff_eq_or_reaches₁, H, false_or] at c₂h,
  apply reaches₁_fwd c₂h ha₂',
end

theorem tr_eval {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ b₁ a₂} (aa : tr a₁ a₂)
  (ab : b₁ ∈ eval f₁ a₁) : ∃ b₂, tr b₁ b₂ ∧ b₂ ∈ eval f₂ a₂ :=
begin
  cases mem_eval.1 ab with ab b0,
  rcases tr_reaches H aa ab with ⟨b₂, bb, ab⟩,
  refine ⟨_, bb, mem_eval.2 ⟨ab, _⟩⟩,
  rw part.eq_some_iff at ⊢ b0, rwa ← H.none_iff_none bb,
end

theorem tr_eval_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ b₂ a₂} (aa : tr a₁ a₂)
  (ab : b₂ ∈ eval f₂ a₂) : ∃ b₁, tr b₁ b₂ ∧ b₁ ∈ eval f₁ a₁ :=
begin
  cases mem_eval.1 ab with ab b0,
  rcases tr_reaches_rev H aa ab with ⟨c₁, c₂, bc, cc, ac⟩,
  cases (refl_trans_gen_iff_eq _).1 bc,
  swap, { intros _ h, rw b0 at h, simpa using h, },
  refine ⟨_, cc, mem_eval.2 ⟨ac, _⟩⟩,
  rw part.eq_some_iff at b0 ⊢, rwa H.none_iff_none cc,
end

theorem tr_eval_dom {σ₁ σ₂ f₁ f₂} {tr : σ₁ → σ₂ → Prop}
  (H : respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) :
  (eval f₂ a₂).dom ↔ (eval f₁ a₁).dom :=
⟨λ h, let ⟨b₂, tr, h, _⟩ := tr_eval_rev H aa ⟨h, rfl⟩ in h,
 λ h, let ⟨b₂, tr, h, _⟩ := tr_eval H aa ⟨h, rfl⟩ in h⟩

/-- A simpler version of `respects` when the state transition relation `tr` is a function. -/
structure frespects {σ₁ σ₂} (f₁ : σ₁ →. option σ₁) (f₂ : σ₂ →. option σ₂) (tr : σ₁ → σ₂) : Prop :=
(dom_of_dom : ∀ ⦃a : σ₁⦄, (f₂ (tr a)).dom → (f₁ a).dom)
(some_of_some : ∀ ⦃a b : σ₁⦄, some b ∈ f₁ a → reaches₁ f₂ (tr a) (tr b))
(none_of_none : ∀ ⦃a⦄, none ∈ f₁ a → none ∈ f₂ (tr a))

variable {ftr : σ₁ → σ₂}
theorem fun_respects : respects f₁ f₂ (λ a b, ftr a = b) ↔ frespects f₁ f₂ ftr :=
begin
  split,
  { intro H,
    refine ⟨λ a, H.dom_of_dom rfl, λ a b hab, _, λ a ha, H.none_of_none rfl ha⟩, 
    simpa using H.some_of_some rfl hab, },
  { intro H,
    refine ⟨_, _, _⟩, { rintro a₁ a₂ rfl h, exact H.dom_of_dom h, },
    { rintro a₁ a₂ b₁ rfl h, exact ⟨_, rfl, H.some_of_some h⟩, },
    rintro a₁ a₂ rfl h, exact H.none_of_none h, }
end

theorem frespects.eval_eq (H : frespects f₁ f₂ ftr)
  (a₁ : σ₁) : eval f₂ (ftr a₁) = (eval f₁ a₁).map ftr :=
begin
  rw ← fun_respects at H,
  apply part.ext', { exact tr_eval_dom H rfl, },
  intros h₂ h₁, simp at h₁,
  have := tr_eval H rfl (part.get_mem h₁),
  simp at this ⊢, rwa part.get_eq_iff_mem,
end

theorem frespects.of_eval (H : frespects f₁ f₂ ftr)
  {a b : σ₁} (h : b ∈ eval f₁ a) : (ftr b) ∈ eval f₂ (ftr a) :=
by { rw H.eval_eq, exact part.mem_map ftr h, }

theorem frespects.none_iff_none (H : frespects f₁ f₂ ftr) (a : σ₁) :
  none ∈ f₁ a ↔ none ∈ f₂ (ftr a) :=
by { rw ← fun_respects at H, rw H.none_iff_none rfl, }

theorem frespects.eval_dom (H : frespects f₁ f₂ ftr) (x : σ₁) :
  (eval f₂ (ftr x)).dom ↔ (eval f₁ x).dom := by simp [H.eval_eq]

theorem frespects.eval_get_eq (H : frespects f₁ f₂ ftr) (a : σ₁) :
  ∀ h, ftr ((eval f₁ a).get h) = (eval f₂ (ftr a)).get (by rwa H.eval_dom) :=
by { intros, simp [H.eval_eq], refl, }

section track_with
variables {σ α : Type} (f : σ →. option σ) (t : σ →. ℕ)

def with_time : ℕ × σ →. option (ℕ × σ) :=
λ tx, do r₁ ← f tx.2, r₂ ← t tx.2, part.some (r₁.map $ λ r₁', (tx.1 + r₂, r₁'))

theorem with_time_respects {f : σ →. option σ} {t : σ →. ℕ} (ht : ∀ x, (t x).dom ↔ (f x).dom) : frespects (with_time f t) f prod.snd :=
{ dom_of_dom := λ a, by simp [with_time, ht],
  some_of_some := λ ⟨a₁, x₁⟩ ⟨a₂, x₂⟩ h, by { apply reaches₁_single, simp [with_time] at h, rcases h with ⟨_, h, _, _, rfl, rfl⟩, exact h, },
  none_of_none := λ ⟨a, x⟩, by { simp [with_time], exact λ h _ _, h, } }

theorem with_time_respects_self (n : ℕ) : frespects (with_time f t) (with_time f t) (prod.map (+n) id) :=
{ dom_of_dom := λ a, by { simp [with_time], exact and.intro, },
  some_of_some := λ ⟨a₁, x₁⟩ ⟨a₂, x₂⟩ h, 
begin
  apply reaches₁_single,
  simp [with_time] at h ⊢,
  rcases h with ⟨a, ha, t, ht₁, rfl, rfl⟩,
  exact ⟨_, ha, t, ht₁, rfl, by ac_refl⟩,
end,
  none_of_none := by { simp [with_time], tauto, } }

def time_iter : σ →. ℕ :=
λ s, (eval (with_time f t) (0, s)) >>= λ r, (t r.2).map (+r.1)

variables {f t}
theorem time_iter_dom_iff (ht : ∀ x, (t x).dom ↔ (f x).dom) {x} :
  (time_iter f t x).dom ↔ (eval f x).dom :=
begin
  simp [time_iter],
  have := with_time_respects ht,
  simp_rw [← this.eval_dom (0, x), this.eval_get_eq (0, x), ht, eval_next_iter_eq_none f x], simp,
end

theorem time_iter_eq_iff (ht : ∀ x, (t x).dom ↔ (f x).dom) (x : σ) (n : ℕ) :
  n ∈ time_iter f t x ↔ ∃ t' b, reaches (with_time f t) (0, x) (t', b) ∧ none ∈ f b ∧ n ∈ (+t') <$> (t b) :=
begin
  simp [time_iter, mem_eval],
  apply exists₂_congr, intros a b,
  conv_lhs { rw and_assoc, }, apply and_congr, { refl, },
  apply and_congr, { rw ← (with_time_respects ht).none_iff_none (a, b), exact part.eq_some_iff, }, { refl, },
end

theorem time_iter_eq_iff_of_eval (ht : ∀ x, (t x).dom ↔ (f x).dom) {x n b} (hb : b ∈ eval f x) :
  n ∈ time_iter f t x ↔ ∃ t', reaches (with_time f t) (0, x) (t', b) ∧ none ∈ f b ∧ n ∈ (+t') <$> (t b) :=
begin
  suffices : ∀ {t' b'}, reaches (with_time f t) (0, x) (t', b') → none ∈ f b' → b = b',
  { rw time_iter_eq_iff ht, apply exists_congr, intro n, split, { rintro ⟨b, h₁, h₂, h₃⟩, cases this h₁ h₂, tauto, }, intro, use b, tauto, },
  intros n b' h₁ h₂, rw [← (with_time_respects ht).none_iff_none (n, b'), ← part.eq_some_iff] at h₂,
  exact part.mem_unique hb ((with_time_respects ht).of_eval (mem_eval.mpr ⟨h₁, h₂⟩)),
end

end track_with

end part_eval