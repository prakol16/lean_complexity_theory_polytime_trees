import data.polynomial.eval
import time_bound
import npolynomial

def polytime (c : code) : Prop :=
∃ (p : polynomial ℕ), time_bound c (λ n, p.eval n)

lemma polytime.dom_univ {c : code} (p : polytime c) : c.eval.dom = set.univ :=
by { cases p with p h, exact eval_dom_of_time_bound h, }

lemma polytime.dom_univ' {c : code} (p : polytime c) : ∀ x, (c.eval x).dom :=
by { intro x, change x ∈ c.eval.dom, rw p.dom_univ, trivial, }

@[simp] def polytime.to_fun {c : code} (pc : polytime c) (x : ptree) : ptree :=
(c.eval x).get (pc.dom_univ' _)

lemma polytime_left : polytime code.left :=
⟨polynomial.monomial 1 1, by simpa using time_bound_left⟩

lemma polytime_right : polytime code.right := polytime_left

lemma polytime_id : polytime code.id := polytime_left

lemma polytime_nil : polytime code.nil := ⟨1, by simpa using time_bound_nil⟩

lemma polytime_node {c₁ c₂ : code} : polytime c₁ → polytime c₂ → polytime (code.node c₁ c₂)
| ⟨p₁, e₁⟩ ⟨p₂, e₂⟩ := by { use p₁ + p₂ + 1, convert time_bound_node e₁ e₂, simp, }

lemma polytime_comp {c₁ c₂ : code} : polytime c₁ → polytime c₂ → polytime (code.comp c₁ c₂)
| ⟨p₁, e₁⟩ ⟨p₂, e₂⟩ := by { use (p₁.comp p₂) + p₂ + 1, convert time_bound_comp (monotone_polynomial_nat _) e₁ e₂, simp, }

lemma polytime_case {c₁ c₂ : code} : polytime c₁ → polytime c₂ → polytime (code.case c₁ c₂)
| ⟨p₁, e₁⟩ ⟨p₂, e₂⟩ := by { use p₁ + p₂ + 1, convert time_bound_case' (monotone_polynomial_nat _) (monotone_polynomial_nat _) e₁ e₂, simp, }

lemma polytime_const (v : ptree) : polytime (code.const v) :=
by { induction v, { exact polytime_nil, }, apply polytime_node; assumption }

lemma polytime_ite {c₁ c₂ c₃ : code} (p₁ : polytime c₁) (p₂ : polytime c₂) (p₃ : polytime c₃) :
  polytime (code.ite c₁ c₂ c₃) :=
polytime_comp (polytime_case p₂ p₃) (polytime_node p₁ polytime_id)
