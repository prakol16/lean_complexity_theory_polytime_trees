import polycodable

variables {α β γ δ ε : Type*} [polycodable α] [polycodable β] [polycodable γ]
 [polycodable δ] [polycodable ε]

open polycodable (encode)

@[simp] lemma encode_sizeof_ptree (x : ptree) : (encode x).sizeof = x.sizeof := rfl
lemma one_le_encode_sizeof (x : α) :
  1 ≤ (encode x).sizeof :=
by { cases (encode x); simp, linarith only, }

@[simp] lemma encode_sizeof_pair (a : α) (b : β) : (encode (a, b)).sizeof = (encode a).sizeof + (encode b).sizeof + 1 :=
by { simp [encode], ac_refl, }

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

lemma polysize_fun_of_fin_range [fintype β] (f : α → β) : polysize_fun f :=
begin
  haveI : nonempty β := ⟨polycodable.decode ptree.nil⟩,
  let B := ((finset.image (λ x : β, (encode x).sizeof) finset.univ).max' _ : ℕ),
  { use B, intro x, simp, apply finset.le_max', simp, },
  simpa using finset.univ_nonempty,
end

