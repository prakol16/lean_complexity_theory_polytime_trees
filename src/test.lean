import data.pfun
import data.real.basic
import tactic.polyrith

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


section

lemma mul_inv_one_of_ne {k : Type*} [field k] {a b : k} (h : a ≠ b) : (a - b) * (a - b)⁻¹ = 1 :=
by simp [sub_ne_zero_of_ne h]

theorem mathd_train_algebra_217
  (a b : ℝ)
  (f g : ℝ → ℝ)
  (h₀ : ∀ x, f x = a * x + b)
  (h₁ : ∀ x, g x = b * x + a)
  (h₂ : a ≠ b)
  (h₃ : ∀ x, f (g x) - g (f x) = b - a) :
  a + b = 0 :=
begin
  simp_rw [h₀, h₁] at h₃,
  polyrith [h₃ 0, mul_inv_one_of_ne h₂],
end

example (a b : ℤ) (h : a * b = 1) (h₂ : a = 0) : (1 : ℤ) = 0 :=
by { linear_combination -h + b * h₂, }

structure line := (a : ℝ) (b : ℝ)
def line.contains (l : line) (p : ℝ × ℝ) : Prop :=
p.snd = l.a * p.fst + l.b

-- example {x₀ x₁ y₀ y₁ : ℝ} (h : x₀ ≠ x₁) : set.subsingleton {l : line | l.contains (x₀, y₀) ∧ l.contains (x₁, y₁) } :=
-- by { rintros ⟨a, b⟩ ⟨H₁, H₂⟩ ⟨a', b'⟩ ⟨H₁', H₂'⟩, simp [line.contains] at *, split; polyrith [mul_inv_one_of_ne h], }

example {x : ℝ} (hx : x^2 = 0) : x = 0 :=
by { by_contra, apply @one_ne_zero ℝ, polyrith [mul_inv_one_of_ne h], }

end