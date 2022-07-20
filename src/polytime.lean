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

-- lemma polytime_ite' {c₁ c₂ c₃ : code} (p₁ : polytime c₁) (p₂ p₃ : polynomial ℕ)
--   (hp₂ : ∀ (n : ℕ) (x : ptree), x.sizeof ≤ n → ptree.nil ∈ c₁.eval x → ∃ t ∈ c₂.time x, t ≤ p₂.eval n)
--   (hp₃ : ∀ (n : ℕ) (x : ptree), x.sizeof ≤ n → ptree.nil ∉ c₁.eval x → ∃ t ∈ c₃.time x, t ≤ p₃.eval n) :
--   polytime (c₁.ite c₂ c₃) :=
-- begin
--   have ite_dom_univ : (c₁.ite c₂ c₃).eval.dom = set.univ,
--   { rw dom_univ_iff, intro x, rw ite_dom,
--     obtain ⟨r, hr⟩ := part.dom_iff_mem.mp (p₁.dom_univ' x), use [r, hr],
--     split,
--     { rintro rfl, rw [← time_dom_iff_eval_dom, part.dom_iff_mem],
--       obtain ⟨y, hy, _⟩ := hp₂ _ _ rfl.le hr, exact ⟨y, hy⟩, },
--     { intro h, rw [← time_dom_iff_eval_dom, part.dom_iff_mem],
--       obtain ⟨y, hy, _⟩ := hp₃ _ x rfl.le (λ C, h (part.mem_unique hr C)), exact ⟨y, hy⟩, } },
--   have cond_dom_univ : ∀ x, (c₁.eval x).dom := p₁.dom_univ',
--   rcases p₁ with ⟨p₁, e₁⟩,
--   use p₁ + p₂ + p₃ + (polynomial.monomial 1 1) + 3,
--   intros n v hnv,
--   rw [← time_dom_eq_eval_dom, dom_univ_iff] at ite_dom_univ, specialize ite_dom_univ v,
--   rw part.dom_iff_mem at ite_dom_univ, cases ite_dom_univ with t H, use [t, H],
--   specialize cond_dom_univ v, specialize e₁ n v hnv, specialize hp₂ n v hnv, specialize hp₃ n v hnv,
--   obtain ⟨r, hr⟩ := part.dom_iff_mem.mp cond_dom_univ,
--   obtain ⟨tc, htc, tc_le⟩ := e₁,
--   rw ← part.eq_some_iff at hr htc,
--   simp [code.ite, code.time, hr, htc, add_def] at H,
--   rcases H with ⟨t, ht, rfl⟩,
--   suffices : t ≤ p₂.eval n + p₃.eval n,
--   { simp at ⊢, linarith only [this, tc_le, hnv], },
--   split_ifs at ht,
--   { subst h, simp [hr] at hp₂, rcases hp₂ with ⟨t, ht', Ht⟩, cases part.mem_unique ht ht',
--     nlinarith only [Ht], },
--   { rw (@comm _ (=)) at h, simp [hr, h] at hp₃, rcases hp₃ with ⟨t, ht', Ht⟩, cases part.mem_unique ht ht',
--     nlinarith only [Ht], },
-- end
