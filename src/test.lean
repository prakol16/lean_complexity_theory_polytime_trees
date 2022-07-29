import data.pfun

namespace pfun
variables {α β γ δ ε ι : Type*}

/-- Product of partial functions. -/
protected def prod (f : α →. γ) (g : β →. δ) : α × β →. γ × δ :=
λ x, ⟨(f x.1).dom ∧ (g x.2).dom, λ h, ((f x.1).get h.1, (g x.2).get h.2)⟩

@[simp] lemma dom_prod (f : α →. γ) (g : β →. δ) :
  (f.prod g).dom = {x | (f x.1).dom ∧ (g x.2).dom} := rfl

lemma get_prod (f : α →. γ) (g : β →. δ) (x : α × β) (h) :
  (f.prod g x).get h = ((f x.1).get h.1, (g x.2).get h.2) := rfl

lemma prod_apply (f : α →. γ) (g : β →. δ) (x : α × β) :
  f.prod g x = ⟨(f x.1).dom ∧ (g x.2).dom, λ h, ((f x.1).get h.1, (g x.2).get h.2)⟩ := rfl

@[simp] lemma mem_prod_iff {f : α →. γ} {g : β →. δ} {x : α × β} {y : γ × δ} :
  y ∈ f.prod g x ↔ y.1 ∈ f x.1 ∧ y.2 ∈ g x.2 :=
by { simp [prod_apply], tidy, }

lemma mem_prod {f : α →. γ} {g : β →. δ} {x : α × β} {y : γ × δ} :
  y ∈ f.prod g x ↔ ∃ h : (f.prod g x).dom, ((f x.1).get h.1, (g x.2).get h.2) = y := iff.rfl

@[simp] lemma prod_id_id : (pfun.id α).prod (pfun.id β) = pfun.id _ :=
ext $ λ ⟨_, _⟩ ⟨_, _⟩, by simp

@[simp] lemma prod_comp_comp (f₁ : α →. β) (f₂ : β →. γ) (g₁ : δ →. ε) (g₂ : ε →. ι) :
  (f₂.comp f₁).prod (g₂.comp g₁) = (f₂.prod g₂).comp (f₁.prod g₁) :=
ext $ λ ⟨_, _⟩ ⟨_, _⟩, by { simp, tauto, }


end pfun