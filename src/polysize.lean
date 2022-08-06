import polycodable

open ptree (pencodable)

variables {α β γ δ ε : Type*} [pencodable α] [pencodable β] [pencodable γ]
 [pencodable δ] [pencodable ε]

open ptree.pencodable (encode decode)

class has_psize (α : Type*) [pencodable α] :=
(psize : α → ℕ)
(p_lower : ∃ p : polynomial ℕ, ∀ x, (encode x).sizeof ≤ p.eval (psize x))
(p_upper : ∃ p : polynomial ℕ, ∀ x, psize x ≤ p.eval (encode x).sizeof)

def default_has_psize (α : Type*) [pencodable α] : has_psize α :=
{ psize := λ x, (encode x).sizeof,
  p_lower := ⟨polynomial.monomial 1 1, λ x, le_of_eq (by simp)⟩,
  p_upper := ⟨polynomial.monomial 1 1, λ x, le_of_eq (by simp)⟩ }

-- def mk_has_psize_of_fintype (α : Type*) [fintype α] [pencodable α] (psize : α → ℕ) : has_psize α :=
-- begin
--   refine_struct { psize := psize }, sorry,
--   -- suffices : ∀ (f g : α → ℕ), ∃ p : polynomial ℕ, 
-- end

open has_psize (psize)

section psize
variables [has_psize α] [has_psize β]

noncomputable def psize_lower (α : Type*) [pencodable α] [has_psize α] : polynomial ℕ :=
  (infer_instance : has_psize α).p_lower.some
lemma psize_lower_spec (x : α) : (encode x).sizeof ≤ (psize_lower α).eval (psize x) :=
    (infer_instance : has_psize α).p_lower.some_spec x
noncomputable def psize_upper (α : Type*) [pencodable α] [has_psize α] : polynomial ℕ :=
  (infer_instance : has_psize α).p_upper.some
lemma psize_upper_spec (x : α) : psize x ≤ (psize_upper α).eval (encode x).sizeof :=
    (infer_instance : has_psize α).p_upper.some_spec x

instance : has_psize ptree := default_has_psize _
instance : has_psize (α × β) :=
{ psize := λ x, psize x.1 + psize x.2,
  p_lower := ⟨1 + (psize_lower α + psize_lower β), λ ⟨x₁, x₂⟩, 
  begin
    simp [encode, add_assoc],
    mono; refine (psize_lower_spec _).trans _; mono; simp,
  end⟩,
  p_upper := ⟨psize_upper α + psize_upper β, λ ⟨x₁, x₂⟩,
  begin
    simp,
    mono; refine (psize_upper_spec _).trans _; mono; simp [encode]; linarith only,
  end⟩ }
-- instance {α : Type*} [pencodable α] : has_psize (list α) := 

end psize

@[simp] lemma encode_sizeof_ptree (x : ptree) : (encode x).sizeof = x.sizeof := rfl
lemma one_le_encode_sizeof (x : α) :
  1 ≤ (encode x).sizeof :=
by { cases (encode x); simp, linarith only, }

@[simp] lemma encode_sizeof_pair (a : α) (b : β) : (encode (a, b)).sizeof = (encode a).sizeof + (encode b).sizeof + 1 :=
by { simp [encode], ac_refl, }

@[simp] lemma encode_sizeof_unit (x : unit) : (encode x).sizeof = 1 :=
by simp [encode]

@[simp] lemma polysize_fun.encode_tt_sizeof : (encode tt).sizeof = 1 :=
by simp [encode]

@[simp] lemma polysize_fun.encode_ff_sizeof : (encode ff).sizeof = 3 :=
by simp [encode]

@[simp] lemma encode_sizeof_nil : (encode ([] : list γ)).sizeof = 1 :=
by simp [encode]
@[simp] lemma encode_sizeof_cons (a : γ) (b : list γ) :
  (encode (a :: b)).sizeof = 1 + (encode a).sizeof + (encode b).sizeof :=
by simp [encode]

lemma encode_sizeof_le_of_mem {l : list γ} {x : γ} (hx : x ∈ l) :
  (encode x).sizeof ≤ (encode l).sizeof :=
begin
  induction l with hd tl ih, { simp at hx, contradiction, },
  rcases ((list.mem_cons_iff _ _ _).mp hx) with rfl|h; simp,
  { linarith only, },
  linarith only [ih h],
end

@[simp] lemma encode_sizeof_append (a b : list γ) :
  ((encode (a ++ b)).sizeof : ℤ) = ((encode a).sizeof : ℤ) + (encode b).sizeof - 1 :=
by { induction a with hd tl ih, { simp, }, simp [ih], ring, }

lemma encode_sizeof_le_of_sublist {a b : list γ} (h : a <+ b) :
  (encode a).sizeof ≤ (encode b).sizeof :=
begin
  induction h, { simp, },
  case list.sublist.cons : l₁ l₂ s₁ H ih { refine ih.trans _, simp, },
  case list.sublist.cons2 : l₁ l₂ s₁ H ih { simpa, },
end

lemma encode_sizeof_le_of_infix {a b : list γ} (h : a <:+: b) :
  (encode a).sizeof ≤ (encode b).sizeof :=
encode_sizeof_le_of_sublist h.sublist

lemma encode_list_sizeof (l : list γ) : 
  (encode l).sizeof = (l.map (λ x, (encode x).sizeof)).sum + l.length + 1 :=
by { induction l with hd tl ih, { simp, }, simp [ih], ac_refl, }

@[simp] lemma encode_sizeof_reverse (l : list γ) :
  (encode l.reverse).sizeof = (encode l).sizeof :=
by { simp [encode_list_sizeof, list.sum_reverse], }

lemma len_le_encode_sizeof' (a : list γ) :
  a.length + 1 ≤ (encode a).sizeof :=
by { induction a with hd tl ih, { simp, }, simp, linarith, }

lemma len_le_encode_sizeof (a : list γ) :
  a.length ≤ (encode a).sizeof :=
by { refine trans _ (len_le_encode_sizeof' a), simp, }

def polysize_fun (f : α → β) : Prop :=
∃ p : polynomial ℕ, ∀ (x : α), (encode (f x)).sizeof ≤ p.eval (encode x).sizeof

lemma polysize_of_polytime_fun {f : α → β} (hf : polytime_fun f) :
  polysize_fun f :=
begin
  rcases hf with ⟨c, ⟨p, hp⟩, sc⟩, use p,
  intro x, specialize sc x, rw part.eq_some_iff at sc,
  rcases hp (encode x) with ⟨t, ht, t_le⟩,
  exact (eval_sizeof_le_time sc ht).trans t_le,
end

lemma polysize_fun.comp {g : β → γ} {f : α → β} (hg : polysize_fun g) (hf : polysize_fun f) :
  polysize_fun (g ∘ f) :=
begin
  rcases hf with ⟨pf, hpf⟩, rcases hg with ⟨pg, hpg⟩,
  use pg.comp pf, intro x, simp,
  refine (hpg _).trans (monotone_polynomial_nat _ _),
  apply hpf,
end

def polysize_fun₂ (f : α → β → γ) : Prop := polysize_fun (function.uncurry f)
lemma polysize₂_of_polytime₂ {f : α → β → γ} (hf : polytime_fun₂ f) : polysize_fun₂ f :=
polysize_of_polytime_fun hf

lemma polysize_fun.pair {f : α → β} {g : α → γ} (hf : polysize_fun f) (hg : polysize_fun g) :
  polysize_fun (λ s, (f s, g s)) :=
by { cases hf with pf hpf, cases hg with pg hpg, use pf + pg + 1, intro x, simpa using add_le_add (hpf _) (hpg _), }

lemma polysize_fun.comp₂ {f : α → β → γ} {g : δ → α} {h : δ → β} (hf : polysize_fun₂ f) (hg : polysize_fun g) (hh : polysize_fun h) :
  polysize_fun (λ s, f (g s) (h s)) :=
polysize_fun.comp hf (polysize_fun.pair hg hh)


def polysize_fun₃ (f : α → β → γ → δ) : Prop :=
polysize_fun (λ a : α × β × γ, f a.1 a.2.1 a.2.2)
lemma polysize₃_of_polytime₃ {f : α → β → γ → δ} (hf : polytime_fun₃ f) : polysize_fun₃ f :=
polysize_of_polytime_fun hf
lemma polysize_fun.comp₃ {f : α → β → γ → δ} {g : ε → α} {h : ε → β} {i : ε → γ}
  (hf : polysize_fun₃ f) (hg : polysize_fun g) (hh : polysize_fun h) (hi : polysize_fun i) :
  polysize_fun (λ s, f (g s) (h s) (i s)) :=
polysize_fun.comp hf (polysize_fun.pair hg (polysize_fun.pair hh hi))

variables {σ : α → Type*} [∀ x, pencodable (σ x)]
def polysize_fun_safe (f : Π x, (σ x) → γ) : Prop :=
∃ p : polynomial ℕ, ∀ (x : α) (y : σ x), (encode (f x y)).sizeof ≤ (encode y).sizeof + p.eval (encode x).sizeof

lemma polysize_fun_safe_of_polysize {f : α → γ} :
  polysize_fun f → polysize_fun_safe (λ x (_ : σ x), f x)
| ⟨p, hp⟩ := by { refine ⟨p, λ _ _, (hp _).trans _⟩, simp, }

@[simp] lemma polysize_fun_safe_iff_polysize {f : α → γ} :
  polysize_fun_safe (λ x (_ : β), f x) ↔ polysize_fun f :=
begin
  split, swap, { exact polysize_fun_safe_of_polysize, },
  inhabit β, 
  rintro ⟨p, hp⟩, dsimp only at hp,
  use p + (encode (default : β)).sizeof, intro x,
  simpa [add_comm] using hp x default,
end

def polysize_fun_uniform (f : Π x, (σ x) → γ) : Prop :=
∃ p : polynomial ℕ, ∀ (x : α) (y : σ x), (encode (f x y)).sizeof ≤ p.eval (encode x).sizeof

@[simp] lemma polysize_fun_uniform_iff_polysize {f : α → γ} :
  polysize_fun_uniform (λ x (_ : σ x), f x) ↔ polysize_fun f :=
begin
  split,
  { rintro ⟨p, hp⟩, use p, intro x, inhabit (σ x),
    simpa using hp x default, },
  { rintro ⟨p, hp⟩, exact ⟨p, λ _ _, (hp _).trans rfl.le⟩ },
end

lemma polysize_fun_uniform.to_safe {f : Π x, σ x → γ} : polysize_fun_uniform f → polysize_fun_safe f
| ⟨p, hp⟩ := ⟨p, λ x y, (hp x y).trans (by simp)⟩

lemma polysize_uniform_of_fin_range [fintype γ] (f : Π x, σ x → γ) :
  polysize_fun_uniform f :=
begin
  haveI : nonempty γ := ⟨decode ptree.nil⟩,
  let B := ((finset.image (λ x : γ, (encode x).sizeof) finset.univ).max' _ : ℕ),
  { use B, intros x _, simp, apply finset.le_max', simp, },
  simpa using finset.univ_nonempty,
end

lemma polysize_fun_of_fin_range [fintype β] (f : α → β) : polysize_fun f :=
by simpa using (show polysize_fun_uniform (λ x (y : unit), f x), from polysize_uniform_of_fin_range _)

lemma polysize_fun_uniform.pair {f : Π x, (σ x) → β} {g : Π x, (σ x) → γ} :
  polysize_fun_uniform f → polysize_fun_uniform g → polysize_fun_uniform (λ x y, (f x y, g x y))
| ⟨pf, hpf⟩ ⟨pg, hpg⟩ :=
begin
  use pf + pg + 1,
  intros x y,
  simp, mono,
end

variables {ι : Type*} {ζ : ι → Type*} [pencodable ι] [∀ x, pencodable (ζ x)]
lemma polysize_fun_safe.comp
  {f : α → β → γ} {g : Π x, ζ x → α} {h : Π x, ζ x → β} :
  polysize_fun_safe f → polysize_fun_uniform g → polysize_fun_safe h →
  polysize_fun_safe (λ x y, f (g x y) (h x y))
| ⟨pf, hf⟩ ⟨pg, hg⟩ ⟨ph, hh⟩ :=
begin
  use ph + (pf.comp pg),
  intros x y,
  refine (hf _ _).trans _,
  simp [← add_assoc], mono*,
end

lemma polysize_fun_safe.comp'
  {f : β → γ} {g : Π x, ζ x → β} (hf : polysize_fun_safe (λ (_ : unit), f)) (hg : polysize_fun_safe g) : polysize_fun_safe (λ x y, f (g x y)) :=
by { apply hf.comp, { exact polysize_uniform_of_fin_range default, }, exact hg, }

lemma polysize_fun_uniform.comp {f : α → β → γ} {g : Π x, ζ x → α} {h : Π x, ζ x → β} :
  polysize_fun_uniform f → polysize_fun_uniform g → polysize_fun_uniform (λ x y, f (g x y) (h x y))
| ⟨pf, hf⟩ ⟨pg, hg⟩ :=
begin
  use pf.comp pg, intros x y, simp,
  refine (hf _ _).trans _, mono,
end

lemma polysize_fun_uniform.comp' {f : β → γ} {g : Π x, ζ x → β} :
  polysize_fun_safe (λ (_ : unit), f) → polysize_fun_uniform g → polysize_fun_uniform (λ x y, f (g x y))
| ⟨pf, hf⟩ ⟨pg, hg⟩ :=
begin
  use pg + (pf.eval 1), intros x y, simp at hf hg ⊢,
  refine (hf () (g x y)).trans _, simpa using hg _ _,
end

lemma polysize_fun_safe.pair_left {f : Π x, σ x → γ} {g : Π x, σ x → β}
  (hf : polysize_fun_uniform f) (hg : polysize_fun_safe g) :
  polysize_fun_safe (λ x y, (f x y, g x y)) :=
begin
  rcases hf with ⟨pf, hf⟩, rcases hg with ⟨pg, hg⟩,
  use pg + pf + 1, intros x y, simp [← add_assoc],
  conv_lhs { rw add_comm, }, mono,
end

lemma polysize_fun_safe.pair_right {f : Π x, σ x → γ} {g : Π x, σ x → β}
  (hf : polysize_fun_safe f) (hg : polysize_fun_uniform g) :
  polysize_fun_safe (λ x y, (f x y, g x y)) :=
begin
  rcases hf with ⟨pf, hf⟩, rcases hg with ⟨pg, hg⟩,
  use pf + pg + 1, intros x y, simp [← add_assoc], mono,
end

lemma polysize_fun_safe.tail (α : Type*) [pencodable α] : polysize_fun_safe (λ (_ : α), @list.tail β) :=
⟨0, λ _ y, by simpa using encode_sizeof_le_of_sublist (y.tail_sublist)⟩

lemma polysize_fun_safe.fst (α : Type*) [pencodable α] : polysize_fun_safe (λ (_ : α), @prod.fst β γ) :=
⟨0, λ _ ⟨y₁, y₂⟩, by simp [add_assoc]⟩

lemma polysize_fun_safe.snd (α : Type*) [pencodable α] : polysize_fun_safe (λ (_ : α), @prod.snd β γ) :=
⟨0, λ _ ⟨y₁, y₂⟩, by { simp, linarith only, }⟩

lemma polysize_fun.id : polysize_fun (@id α) :=
⟨polynomial.monomial 1 1, λ x, by simp⟩

lemma polysize_fun_safe.id : polysize_fun_safe (λ (_ : α) (x : β), x) :=
⟨0, λ _ x, by simp⟩

lemma polysize_fun_safe.ite {f g : Π x, σ x → γ} {P : Π x, σ x → Prop} [∀ (x : α) (y : σ x), decidable (P x y)]
  (hf : polysize_fun_safe f) (hg : polysize_fun_safe g) : polysize_fun_safe (λ x y, if P x y then f x y else g x y) :=
begin
  rcases hf with ⟨pf, hf⟩, rcases hg with ⟨pg, hg⟩, use pf + pg,
  intros x y, dsimp only, split_ifs,
  { refine (hf _ _).trans _, simp, }, { refine (hg _ _).trans _, simp, },
end

lemma _root_.bool.cond_eq_ite (x y : α) (b : bool) : cond b x y = if b then x else y := by cases b; refl

lemma polysize_fun_safe.cond {f g : Π x, σ x → γ} {P : Π x, σ x → bool} 
  (hf : polysize_fun_safe f) (hg : polysize_fun_safe g) : polysize_fun_safe (λ x y, cond (P x y) (f x y) (g x y)) :=
by { simp_rw bool.cond_eq_ite, exact polysize_fun_safe.ite hf hg, }

lemma polysize_fun_safe.cons : polysize_fun_safe (@list.cons α) :=
by { use polynomial.monomial 1 1 + 1, intros x y, simp [add_comm], }

def set_encodable (S : set α) [decidable_pred (∈ S)] {d : α} (hd : d ∈ S) : ptree.pencodable S :=
ptree.pencodable.mk'
(coe : S → α)
(λ x, if h : x ∈ S then ⟨x, h⟩ else ⟨d, hd⟩)
(λ x, by simp) 
