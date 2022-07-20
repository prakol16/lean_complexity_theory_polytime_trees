import tactic.linarith
import ite_lemmas
import code

def code.time : code → ptree →. ℕ
| code.left := λ t, part.some t.sizeof
| code.right := λ t, part.some t.sizeof
| code.nil := λ t, part.some 1
| code.id := λ t, part.some t.sizeof
| (code.node a b) := λ t, (+1) <$> (a.time t) + (b.time t)
| (code.comp f g) := λ t, (+1) <$> (g.time t) + (g.eval t >>= f.time)
| (code.case f g) := λ t, (+1) <$> if t.left = ptree.nil then f.time t.right else g.time t.right
| (code.fix f) := λ t, (+t.sizeof) <$> part_eval.time_iter (λ t' : ptree, (f.eval t').map ptree.to_option) f.time t


lemma add_def (x y : part ℕ) : x + y = x >>= λ x', y >>= (λ y', pure (x' + y')) :=
by { simp only [(+), (<*>), part.bind_eq_bind, part.bind_map, part.map_eq_map], congr, ext x, simp, tauto, }

lemma time_dom_iff_eval_dom (c : code) (v : ptree) : (c.time v).dom ↔ (c.eval v).dom :=
begin
  induction c generalizing v,
  all_goals { simp [code.time, add_def], },
  case code.node : c₁ c₂ c₁ih c₂ih { simp [c₁ih, c₂ih], },
  case code.comp : c₁ c₂ c₁ih c₂ih { simp [c₁ih, c₂ih], tauto, },
  case code.case : c₁ c₂ c₁ih c₂ih { simp [c₁ih, c₂ih, apply_ite part.dom], },
  case code.fix : f ih { rw part_eval.time_iter_dom_iff, simp [ih], }
end

lemma time_dom_iff_eval_to_option_dom (c : code) (v : ptree) : (c.time v).dom ↔ ((c.eval v).map ptree.to_option).dom :=
by simp [time_dom_iff_eval_dom]

lemma time_dom_eq_eval_dom (c : code) : c.time.dom = c.eval.dom :=
by { ext, apply time_dom_iff_eval_dom, }

def time_bound (c : code) (bound : ℕ → ℕ) : Prop :=
∀ (v : ptree), ∃ t ∈ c.time v, t ≤ bound v.sizeof

lemma time_bound_of_time_bound_le {c : code} {b₁ : ℕ → ℕ} (hb₁ : time_bound c b₁) {b₂ : ℕ → ℕ} (hb₂ : ∀ n, b₁ n ≤ b₂ n) :
  time_bound c b₂ := λ v, by { obtain ⟨t, ht, t_le⟩ := hb₁ v, use [t, ht], exact t_le.trans (hb₂ _), }

lemma eval_dom_of_time_bound {c : code} {bound : ℕ → ℕ} (h : time_bound c bound) : c.eval.dom = set.univ :=
begin
  ext v, 
  suffices : (c.time v).dom, { simpa [pfun.dom, time_dom_iff_eval_dom], },
  rw part.dom_iff_mem, obtain ⟨t, ht, _⟩ := h v, exact ⟨t, ht⟩,
end

lemma dom_univ_iff {α β : Type*} (f : α →. β) : f.dom = set.univ ↔ ∀ x, (f x).dom :=
by simp [pfun.dom, set.eq_univ_iff_forall]

lemma eval_sizeof_le_time {c : code} {vin vout : ptree} {t : ℕ} (hv : vout ∈ c.eval vin) (ht : t ∈ c.time vin) : vout.sizeof ≤ t :=
begin
  induction c generalizing vin vout t,
  { simp only [code.eval, code.time, part.pure_eq_some, part.mem_some_iff] at hv ht, subst_vars, apply ptree.left_sizeof_le, },
  { simp only [code.eval, code.time, part.pure_eq_some, part.mem_some_iff] at hv ht, subst_vars, apply ptree.right_sizeof_le, },
  { simp [code.time] at hv ht ⊢, subst_vars, simp, },
  { simp [code.time] at hv ht ⊢, subst_vars, },
  case code.node : c₁ c₂ c₁ih c₂ih
  { simp [code.time, add_def] at hv ht,
    rcases ht with ⟨t₁, ht₁, t₂, ht₂, ht⟩,
    rcases hv with ⟨v₁, hv₁, v₂, hv₂, hv⟩,
    specialize c₁ih hv₁ ht₁, specialize c₂ih hv₂ ht₂, rw [hv, ht],
    simp, linarith only [c₁ih, c₂ih], },
  case code.comp : c₁ c₂ c₁ih c₂ih
  { simp [code.time, add_def] at hv ht, 
    rcases ht with ⟨t₁, ht₁, t₂, ⟨v', hv', ht₂⟩, rfl⟩,
    rcases hv with ⟨v'', hv'', H⟩,
    cases part.mem_unique hv' hv'',
    suffices : vout.sizeof ≤ t₂, { linarith only [this], },
    exact c₁ih H ht₂, },
  case code.case : c₁ c₂ c₁ih c₂ih
  { simp [code.time] at hv ht,
    rcases ht with ⟨t', ht', rfl⟩,
    split_ifs at *, { linarith only [c₁ih hv ht'], }, { linarith only [c₂ih hv ht'], } },
  case code.fix : f ih
  { simp [code.time] at hv ht,
    rcases ht with ⟨t, ht, rfl⟩,
    rw part_eval.time_iter_eq_iff_of_eval (time_dom_iff_eval_to_option_dom f) hv at ht,
    rcases ht with ⟨t', hr, hvout', ht⟩,
    rcases relation.refl_trans_gen.cases_tail hr with H | ⟨⟨tl, vl⟩, _, H⟩,
    { simp at H, rw H.2, simp, },
    have t'_le : t' ≤ t, { simp at ht, rcases ht with ⟨_, _, rfl⟩, simp, },
    simp [part_eval.with_time] at H,  rcases H with ⟨vout, hvt, n, hn, ⟨_, rfl⟩, rfl⟩, 
    have := ih hvt hn, 
    linarith only [ptree.right_sizeof_le vout, this, t'_le], }
end

lemma time_bound_left : time_bound code.left id :=
by simp [time_bound, code.time]

lemma time_bound_right : time_bound code.right id := time_bound_left

lemma time_bound_id : time_bound code.id id := time_bound_left

lemma time_bound_nil : time_bound code.nil (λ _, 1) :=
by simp [time_bound, code.time]

lemma time_bound_node {c₁ c₂ : code} {b₁ b₂ : ℕ → ℕ} (hb₁ : time_bound c₁ b₁) (hb₂ : time_bound c₂ b₂) :
  time_bound (code.node c₁ c₂) (λ t, b₁ t + b₂ t + 1) :=
begin
  intros v,
  obtain ⟨t₁, ht₁, hb₁⟩ := hb₁ v,
  obtain ⟨t₂, ht₂, hb₂⟩ := hb₂ v,
  use t₁ + t₂ + 1, split,
  { rw ← part.eq_some_iff at ht₁ ht₂, simp [code.time, ht₁, ht₂, add_def], ring, },
  mono*,
end

lemma time_bound_comp {c₁ c₂ : code} {b₁ b₂ : ℕ → ℕ} (hm : monotone b₁) (hb₁ : time_bound c₁ b₁) (hb₂ : time_bound c₂ b₂) :
  time_bound (c₁.comp c₂) (λ t, b₁ (b₂ t) + b₂ t + 1) :=
begin
  intros v,
  obtain ⟨t₂, ht₂, hb₂⟩ := hb₂ v,
  obtain ⟨v', hv'⟩ := (_ : ∃ v', v' ∈ c₂.eval v), swap,
  { rw [← part.dom_iff_mem, ← time_dom_iff_eval_dom, part.dom_iff_mem], use [t₂, ht₂], },
  obtain ⟨t₁, ht₁, hb₁⟩ := hb₁ v',
  use t₁ + t₂ + 1, split,
  { rw ← part.eq_some_iff at ht₁ ht₂ hv', simp [code.time, ht₁, ht₂, hv', add_def], ring, },
  { mono*, exact hb₁.trans (hm ((eval_sizeof_le_time hv' ht₂).trans hb₂)), },
end

lemma time_bound_case {c₁ c₂ : code} {b₁ b₂ : ℕ → ℕ} (hm₁ : monotone b₁) (hm₂ : monotone b₂) (hb₁ : time_bound c₁ b₁) (hb₂ : time_bound c₂ b₂) :
  time_bound (code.case c₁ c₂) (λ t, max (b₁ t) (b₂ t) + 1) :=
begin
  intros v,
  simp [code.time], split_ifs,
  { obtain ⟨t, ht, H⟩ := hb₁ v.right, use [t, ht], left, exact H.trans (hm₁ $ ptree.right_sizeof_le _), },
  { obtain ⟨t, ht, H⟩ := hb₂ v.right, use [t, ht], right, exact H.trans (hm₂ $ ptree.right_sizeof_le _), },
end

lemma time_bound_case' {c₁ c₂ : code} {b₁ b₂ : ℕ → ℕ} (hm₁ : monotone b₁) (hm₂ : monotone b₂) (hb₁ : time_bound c₁ b₁) (hb₂ : time_bound c₂ b₂) :
  time_bound (code.case c₁ c₂) (λ t, (b₁ t) + (b₂ t) + 1) :=
by { apply time_bound_of_time_bound_le (time_bound_case hm₁ hm₂ hb₁ hb₂), intro, simp, }

-- lemma time_bound_case_precise {c₁ c₂ : code} {b₁ b₂ : ℕ → ℕ} (m₁ : monotone b₁) (m₂ : monotone b₂)
--   (hb₁ : ∀ x : ptree, x.left = ptree.nil → ∃ t ∈ c₁.time x.right, t ≤ b₁ x.sizeof)
--   (hb₂ : ∀ x : ptree, x.left ≠ ptree.nil → ∃ t ∈ c₂.time x.right, t ≤ b₂ x.sizeof) :
--   time_bound (code.case c₁ c₂) (λ n, max (b₁ n) (b₂ n) + 1) :=
-- begin
--   intros n v hnv, 
--   by_cases H : v.left = ptree.nil,
--   { specialize hb₁ v H, rcases hb₁ with ⟨t, ht, s⟩, use t + 1, split,
--     { simpa [code.time, H], }, { simp, left, refine s.trans _, apply m₁ hnv, } },
--   { specialize hb₂ v H, rcases hb₂ with ⟨t, ht, s⟩, use t + 1, split,
--     { simpa [code.time, H], }, { simp, right, refine s.trans _, apply m₂ hnv, } }
-- end
