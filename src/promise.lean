import polytime

def time_bound_promise (c : code) (promise : set ptree) (b : ℕ → ℕ) : Prop :=
∀ x ∈ promise, ∃ t ∈ c.time x, t ≤ b x.sizeof

@[simp] lemma time_bound_promise_univ (c : code) (b : ℕ → ℕ) :
  time_bound_promise c set.univ b ↔ time_bound c b :=
by simp [time_bound, time_bound_promise]

lemma pfun.preimage_def' {α β} {f : α →. β} {S : set β} {x₁} (hx₁ : x₁ ∈ f.preimage S) {x₂} (hx₂ : x₂ ∈ f x₁) :
  x₂ ∈ S :=
by { rcases hx₁ with ⟨x₂, H, hx₂'⟩, cases part.mem_unique hx₂ hx₂', exact H, }

lemma time_bound_promise_comp {c₁ c₂ : code} {P₁ P₂ : set ptree} {b₁ b₂ : ℕ → ℕ} (hm : monotone b₁)
  (hb₁ : time_bound_promise c₁ P₁ b₁) (hb₂ : time_bound_promise c₂ P₂ b₂) :
  time_bound_promise (c₁.comp c₂) (P₂ ∩ c₂.eval.preimage P₁) (λ t, b₁ (b₂ t) + b₂ t + 1) :=
begin
  rintros v ⟨hv₁, hv₂⟩,
  obtain ⟨t₂, ht₂, hb₂⟩ := hb₂ v hv₁,
  obtain ⟨v', hv'⟩ := (_ : ∃ v', v' ∈ c₂.eval v), swap,
  { rw [← part.dom_iff_mem, ← time_dom_iff_eval_dom, part.dom_iff_mem], use [t₂, ht₂], },
  obtain ⟨t₁, ht₁, hb₁⟩ := hb₁ v' (pfun.preimage_def' hv₂ hv'),
  use t₁ + t₂ + 1, split,
  { rw ← part.eq_some_iff at ht₁ ht₂ hv', simp [code.time, ht₁, ht₂, hv', add_def], ring, },
  { mono*, exact hb₁.trans (hm ((eval_sizeof_le_time hv' ht₂).trans hb₂)), },
end

def polytime_promise (c : code) (promise : set ptree) : Prop :=
∃ p : polynomial ℕ, time_bound_promise c promise (λ n, p.eval n)

def polytime_promise_comp {c₁ c₂ : code} {P₁ P₂ : set ptree} :
  polytime_promise c₁ P₁ → polytime_promise c₂ P₂ → polytime_promise (c₁.comp c₂) (P₂ ∩ c₂.eval.preimage P₁)
| ⟨p₁, e₁⟩ ⟨p₂, e₂⟩ := by { use (p₁.comp p₂) + p₂ + 1, convert time_bound_promise_comp (monotone_polynomial_nat _) e₁ e₂, simp, }

