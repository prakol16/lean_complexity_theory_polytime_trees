import data.pfun
import logic.relation
import data.fun_like.basic
import computability.turing_machine

open relation (refl_trans_gen)

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

section hom

structure hom (f : execution σ) (g : execution τ) :=
(to_fun : σ → τ)
(dom_of : ∀ {x}, x ∈ f.states → (g.next (to_fun x)).dom → (f.next x).dom)
(map_fun : ∀ {x} {y : option σ}, x ∈ f.states → y ∈ f.next x → y.map to_fun ∈ g.next (to_fun x))
(start' : to_fun f.start = g.start)

infixr ` →ₛ `:25 := hom

variables {f} {g : execution τ} (h : f →ₛ g)


instance : has_coe_to_fun (f →ₛ g) (λ _, σ → τ) :=
⟨hom.to_fun⟩
@[simp] lemma to_fun_eq_coe : h.to_fun = h := rfl
@[simp] lemma mk_coe (a : σ → τ) (b c d) : ⇑(hom.mk a b c d : f →ₛ g) = a := rfl

lemma hom.dom_iff {x} (hx : x ∈ f.states) : (g.next (h x)).dom ↔ (f.next x).dom :=
begin
  split, { exact h.dom_of hx, },
  intro h, rw part.dom_iff_mem at *,
  rcases h with ⟨y, hy⟩,
  exact ⟨_, h.map_fun hx hy⟩, 
end

lemma hom.mem_next_iff {x} (hx : x ∈ f.states) :
  (∃ y, y ∈ f.next x) ↔ (∃ y, y ∈ g.next (h x)) :=
by { simp_rw [← part.dom_iff_mem, h.dom_iff hx], }

lemma hom.none_iff {x} (hx : x ∈ f.states) :
  none ∈ f.next x ↔ none ∈ g.next (h x) :=
begin
  split, { exact h.map_fun hx, },
  intro H,
  obtain ⟨y, hy⟩ := (h.mem_next_iff hx).mpr ⟨_, H⟩,
  cases y, { assumption, },
  cases part.mem_unique (h.map_fun hx hy) H,
end

lemma hom.some_mem_of {x y} (hx : x ∈ f.states) (hy : some y ∈ g.next (h x)) :
  ∃ z, y = h z ∧ some z ∈ f.next x :=
begin
  obtain ⟨z, hz⟩ := (h.mem_next_iff hx).mpr ⟨_, hy⟩,
  cases z, { rw h.none_iff hx at hz, cases part.mem_unique hy hz, },
  refine ⟨z, _, hz⟩,
  simpa using part.mem_unique hy (by simpa using h.map_fun hx hz),
end

lemma hom.start : h f.start = g.start := h.start'

theorem hom.reaches {x} (hx : x ∈ f.states) : h x ∈ g.states :=
begin
  apply step_induction hx; clear hx x,
  { simpa [h.start] using start_mem_states g, },
  intros x y hs hxy hn,
  apply mem_states_of_fwd hxy, simpa using h.map_fun hs hn,
end

theorem hom.reaches_rev {x} (hx : x ∈ g.states) : ∃ y, h y = x ∧ y ∈ f.states :=
begin
  apply step_induction hx; clear hx x,
  { use f.start, exact ⟨h.start, start_mem_states _⟩, },
  intros x y hxy ih hn,
  rcases ih with ⟨x', rfl, H⟩,
  obtain ⟨z, hz, hz'⟩ := h.some_mem_of H hn,
  exact ⟨_, hz.symm, mem_states_of_fwd H hz'⟩,
end

theorem hom.states_image : h '' f.states = g.states :=
begin
  ext, split,
  { rintro ⟨y, h₁, rfl⟩, exact h.reaches h₁, },
  { intro H, convert h.reaches_rev H, simp, tauto, }
end

theorem hom.mem_eval_iff : f.eval.map h = g.eval :=
begin
  ext y, split,
  { simp only [part.mem_map_iff, exists_prop, forall_exists_index, and_imp],
    rintros x hx rfl, rw [mem_eval] at *, rw ← h.none_iff hx.1, exact ⟨h.reaches hx.1, hx.2⟩, },
  { intro hy,
    simp [mem_eval] at *,
    rcases h.reaches_rev hy.1 with ⟨x, rfl, hx⟩, 
    use x, rw h.none_iff hx, refine ⟨⟨hx, hy.2⟩, rfl⟩, }
end

theorem hom.eval_dom_iff (h : f →ₛ g) : f.eval.dom ↔ g.eval.dom :=
by simp [← h.mem_eval_iff]

@[simps]
def hom.comp {α β γ : Type*} {f : execution α} {g : execution β} {h : execution γ}
  (h₁ : f →ₛ g) (h₂ : g →ₛ h) : f →ₛ h :=
{ to_fun := h₂ ∘ h₁,
  dom_of := λ x hx, by { rw [← h₁.dom_iff hx, ← h₂.dom_iff (h₁.reaches hx)], exact id, },
  map_fun := λ x y hx hy, by { rw [option.comp_map], exact h₂.map_fun (h₁.reaches hx) (h₁.map_fun hx hy), },
  start' := by simp [h₁.start, h₂.start] }

end hom


section track

@[simps]
def with_state (f : execution σ) (state : τ → σ →. τ) (s : τ) : execution (τ × σ) :=
{ next := λ x, (state x.1 x.2).bind (λ s', (f.next x.2).map (λ t', t'.map (prod.mk s'))),
  start := (s, f.start) }

@[simps]
def hom.mk_with_state (f : execution σ) (state : τ → σ →. τ) (s : τ) (H : ∀ s x, (f.next x).dom → (state s x).dom) :
  (f.with_state state s) →ₛ f :=
{ to_fun := prod.snd,
  dom_of := λ ⟨s, x⟩, by { simp, tauto, },
  map_fun := λ x y, by { intro _, simp, rintros _ _ (_|_) _ rfl; simpa, },
  start' := by { simp, } }

@[simps]
def with_time (f : execution σ) (time : σ →. ℕ) :=
f.with_state (λ (n : ℕ) (s : σ), (time s).map (+n)) 0

@[simps]
def hom.mk_with_time (f : execution σ) (time : σ →. ℕ) (H : ∀ s, (f.next s).dom → (time s).dom) :
  (f.with_time time) →ₛ f :=
hom.mk_with_state f _ 0 (by simpa) 


end track


end execution

namespace streams

structure exec_stram (α : Type*) :=
(seq : ℕ → option α)
(sound : ∀ n m, n ≤ m → seq n = none → seq m = none)

end streams