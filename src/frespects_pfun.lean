import data.pfun

/-! Need to figure out how to port over the stuff from `turing.reaches` and `turing.eval` to the slightly more
general setting with any generic `pfun` (i.e. instead of iterating `f : α → option α`, we should be able to
iterate `f : α → β ⊕ α` and more easily convert between `f.fix x`, a sequence of applications `ℕ → α` given by
`x, f(x), f(f(x)), ...`, and a `reaches`-prop `reaches x y` which indicates that `y = f(f(...f(x)))` for some number
of `f`'s.

These are useful in the `pfun` setting, not just Turing machine states.
-/


namespace pfun
lemma exists_preimage_of_fix_dom {α β : Type*} {f : α →. β ⊕ α} {a : α} {b : β} (h : b ∈ f.fix a) :
  ∃ a', sum.inl b ∈ f a' :=
by apply fix_induction' _ _ h; tauto

variables {α₁ α₂ β₁ β₂ : Type*}
variables (f₁ : α₁ →. β₁ ⊕ α₁) (f₂ : α₂ →. β₂ ⊕ α₂)

/-- We just extract a very special case, which is all we need here: two functions `f₁` and `f₂` satisfy
`frespects_once` wrt `F` if whenever `f₁` takes a single step from `a₁ : α₁` to `a₁' : α₁`, `f₂` takes
the corresponding step from `a₂ = F a₁` to `a₂' = F a₁'`, and moreover, if `f₁` diverges on a state iff `f₂` diverges
on the corresponding one, and `f₁` halts on a state iff `f₂` halts on the corresponding one. 

We use a slightly weaker definition which is equivalent to the above description. -/
def frespects_once (F : α₁ → α₂) : Prop :=
∀ a₁, ((f₂ (F a₁)).dom → (f₁ a₁).dom) ∧ (∀ a₁', sum.inr a₁' ∈ f₁ a₁ → (sum.inr $ F a₁') ∈ (f₂ (F a₁)))
  ∧ ((∃ b₁, sum.inl b₁ ∈ f₁ a₁) → ∃ b₂, sum.inl b₂ ∈ f₂ (F a₁))

def frespects_once' (F : α₁ → α₂) (G : β₁ → β₂) : Prop :=
∀ a₁, ((f₂ (F a₁)).dom → (f₁ a₁).dom) ∧ (∀ a₁', sum.inr a₁' ∈ f₁ a₁ → (sum.inr $ F a₁') ∈ (f₂ (F a₁)))
  ∧ (∀ b₁, sum.inl b₁ ∈ f₁ a₁ → sum.inl (G b₁) ∈ f₂ (F a₁))

lemma frespects_once_of_frespects_once' {F : α₁ → α₂} {G : β₁ → β₂} (hFG : frespects_once' f₁ f₂ F G) :
  frespects_once f₁ f₂ F :=
by { intro a₁, specialize hFG a₁, refine ⟨hFG.1, hFG.2.1, _⟩, rintro ⟨b₁, hb₁⟩, use (G b₁), exact hFG.2.2 b₁ hb₁, }

section
variables {F : α₁ → α₂} (hF : frespects_once f₁ f₂ F) {f₁ f₂}
include hF

lemma dom_iff_dom (a : α₁) : (f₁ a).dom ↔ (f₂ (F a)).dom :=
begin
  specialize hF a, split, swap, { exact hF.1, },
  { intro h, 
    rw part.dom_iff_mem at h ⊢,
    obtain ⟨y, hy⟩ := h,
    cases y with ly ry,
    { obtain ⟨b₂, hb₂⟩ := hF.2.2 ⟨ly, hy⟩, use sum.inl b₂, assumption, },
    exact ⟨_, hF.2.1 ry hy⟩, }
end

lemma fwd_preimage_of_fwd {a : α₁} {a' : α₂} (ha' : sum.inr a' ∈ f₂ (F a)) : ∃ a₁', sum.inr a₁' ∈ f₁ a ∧ F a₁' = a' :=
begin
  have : (f₁ a).dom, { rw [dom_iff_dom hF a, part.dom_iff_mem], exact ⟨_, ha'⟩, }, 
  specialize hF a,
  suffices h : ∃ a₁', sum.inr a₁' ∈ f₁ a, 
  { obtain ⟨a₁', h⟩ := h, use a₁', refine ⟨h, _⟩, exact sum.inr_injective (part.mem_unique (hF.2.1 a₁' h) ha'), },
  cases (f₁ a) with d v, cases e : v this with vb va,
  { exfalso, cases hF.2.2 ⟨vb, _⟩ with _ H, { have := part.mem_unique ha' H, contradiction, },
    use this, exact e, },
  use va, use this, exact e,
end

lemma fwd_iff_fwd (a : α₁) : (∃ a', sum.inr a' ∈ f₁ a) ↔ ∃ a', sum.inr a' ∈ f₂ (F a) :=
begin
  split; rintro ⟨a', ha'⟩,
  { exact ⟨_, (hF a).2.1 a' ha'⟩, },
  { obtain ⟨a₁', ha₁'⟩ := fwd_preimage_of_fwd hF ha', exact ⟨a₁', ha₁'.1⟩, }
end

lemma stop_iff_stop (a : α₁) : (∃ b₁, sum.inl b₁ ∈ f₁ a) ↔ ∃ b₂, sum.inl b₂ ∈ f₂ (F a) :=
begin
  split, { exact (hF a).2.2, },
  rintro ⟨b₂, hb₂⟩,
  have : (f₁ a).dom, { rw [dom_iff_dom hF a, part.dom_iff_mem], exact ⟨_, hb₂⟩, }, 
  have H := (fwd_iff_fwd hF a).mp,
  cases (f₁ a) with d v, cases e : v this with vb va,
  { use vb, use this, exact e, },
  exfalso, specialize H ⟨va, _⟩, { use this, exact e, },
  obtain ⟨a₂', ha₂'⟩ := H, have := part.mem_unique hb₂ ha₂', contradiction,
end

lemma frespects_last_step {a : α₁} {b₁ : β₁} {b₂ : β₂} (hb₁ : b₁ ∈ f₁.fix a) (hb₂ : b₂ ∈ f₂.fix (F a)) :
  ∃ a' : α₁, sum.inl b₁ ∈ f₁ a' ∧ sum.inl b₂ ∈ f₂ (F a') :=
begin
  revert hb₂,
  apply fix_induction' _ _ hb₁; clear hb₁ a,
  { intros a' ha' hb₂, use [a', ha'],
    obtain ⟨b₂', hb₂'⟩ := (stop_iff_stop hF a').mp ⟨b₁, ha'⟩,
    have : b₂ = b₂' := part.mem_unique hb₂ (fix_stop _ hb₂'), subst this,
    assumption, },
  intros a a' ha' ha ih hb₂,
  refine ih _,
  rwa ← fix_fwd _ _ ((hF a).2.1 _ ha),
end

variable (F)
theorem eq_dom_of_frespects_once (a : α₁) :
  (f₁.fix a).dom ↔ (f₂.fix (F a)).dom :=
begin
  split; intro h;
    rw part.dom_iff_mem at h;
    cases h with y h,
  { apply fix_induction' _ _ h; clear h a,
    { intros a h, obtain ⟨b₂, hb₂⟩ := (stop_iff_stop hF a).mp ⟨_, h⟩,
      rw [part.dom_iff_mem], use b₂, exact fix_stop _ hb₂, },
    intros a a' hy ha ha',
    rw part.dom_iff_mem at ⊢ ha',
    rw fix_fwd, { exact ha', }, exact (hF a).2.1 a' ha, },
  suffices : ∀ a', F a' = F a → (f₁.fix a').dom, { exact this a rfl, },
  apply @fix_induction' _ _ f₂ y (λ z, ∀ a', F a' = z → (f₁.fix a').dom) _ h; clear h a,
  { intros a ha a' ha', subst ha',
    have : ∃ y', sum.inl y' ∈ f₁ a', { rw stop_iff_stop hF a', exact ⟨_, ha⟩, },
    rw part.dom_iff_mem, obtain ⟨y', hy'⟩ := this, exact ⟨y', fix_stop _ hy'⟩, },
  intros a a' ha' ha ih x hx, subst hx,
  rw part.dom_iff_mem,
  obtain ⟨y', hy', hyF⟩ := fwd_preimage_of_fwd hF ha,
  specialize ih y' hyF,
  rw part.dom_iff_mem at ih, 
  rwa fix_fwd _ _ hy'
end
end

variables {F : α₁ → α₂} {G : β₁ → β₂} {f₁ f₂}
theorem eq_val_of_frespects_once' (hFG : frespects_once' f₁ f₂ F G) (a : α₁) :
  (pfun.fix f₁ a).map G = pfun.fix f₂ (F a) :=
begin
  have := frespects_once_of_frespects_once' _ _ hFG,
  apply part.ext', { exact eq_dom_of_frespects_once _ this a, },
  intros h₁ h₂, simp only [part.map_get, function.comp_app, part.map_dom] at h₁ ⊢,
  set v₁ := (f₁.fix a).get h₁ with hv₁, set v₂ := (f₂.fix (F a)).get h₂ with hv₂, change G v₁ = v₂,
  rw part.eq_get_iff_mem at hv₁ hv₂,
  obtain ⟨l, hl₁, hl₂⟩ := frespects_last_step this hv₁ hv₂,
  simpa using part.mem_unique ((hFG l).2.2 v₁ hl₁) hl₂,
end

end pfun
