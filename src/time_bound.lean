import tactic.linarith
import frespects_pfun
import code

def code.time : code → ptree →. ℕ
| code.left := λ t, part.some t.sizeof
| code.right := λ t, pure t.sizeof
| code.nil := λ t, pure 1
| code.id := λ t, pure t.sizeof
| (code.node a b) := λ t, (+1) <$> (a.time t) + (b.time t)
| (code.comp f g) := λ t, (+1) <$> (g.time t) + (g.eval t >>= f.time)
| (code.case f g) := λ t, (+1) <$> if t.left = ptree.nil then f.time t.right else g.time t.right
| (code.fix f) := λ t, (+1) <$> (pfun.fix $
    λ vt : ptree × ℕ, do
      t' ← f.time vt.1,
      v' ← f.eval vt.1,
      if v'.left = ptree.nil then return $ sum.inl (vt.2 + t')
      else return $ sum.inr (v'.right, vt.2 + t')) (t, 0) 

@[reducible] def time_fix_fun (f : code) (vt : ptree × ℕ) : part (ℕ ⊕ ptree × ℕ) := 
do  t' ← f.time vt.1,
    v' ← f.eval vt.1,
    if v'.left = ptree.nil then return $ sum.inl (vt.2 + t')
    else return $ sum.inr (v'.right, vt.2 + t')

@[reducible] def eval_fix_fun (f : code) (v : ptree) : part (ptree ⊕ ptree) :=
(f.eval v).map (λ v', if v'.left = ptree.nil then sum.inl v'.right else sum.inr v'.right)

lemma code_fix_time (f : code) (v : ptree) : (code.fix f).time v = (+1) <$> pfun.fix (time_fix_fun f) (v, 0) := rfl
lemma code_fix_eval (f : code) : (code.fix f).eval = pfun.fix (eval_fix_fun f) := rfl

@[simp] lemma ite_dom {α : Type*} (c : Prop) [decidable c] (x y : part α) :
  (if c then x else y).dom ↔ if c then x.dom else y.dom :=
by split_ifs; refl

@[simp] lemma sum_inl_eq_ite {α β : Type*} (c : Prop) [decidable c] (x z : α) (y : β) :
  (sum.inl z = if c then sum.inl x else sum.inr y) ↔ c ∧ z = x := by split_ifs; simp; tauto

@[simp] lemma sum_inl_eq_ite_symm {α β : Type*} (c : Prop) [decidable c] (x z : α) (y : β) :
  ((if c then sum.inl x else sum.inr y) = sum.inl z) ↔ c ∧ z = x := by split_ifs; tauto

@[simp] lemma sum_inr_eq_ite {α β : Type*} (c : Prop) [decidable c] (x : α) (y z : β) :
  (sum.inr z = if c then sum.inl x else sum.inr y) ↔ ¬c ∧ z = y := by split_ifs; simp; tauto

@[simp] lemma sum_inr_eq_ite_symm {α β : Type*} (c : Prop) [decidable c] (x : α) (y z : β) :
  ((if c then sum.inl x else sum.inr y) = sum.inr z) ↔ ¬c ∧ z = y := by split_ifs; tauto


example {α β : Type*} (c : Prop) [decidable c] (x y : α) (f : α → β) :
  f (if c then x else y) = if c then f x else f y := by refine apply_ite f c x y

lemma add_def (x y : part ℕ) : x + y = x >>= λ x', y >>= (λ y', pure (x' + y')) :=
by { simp only [(+), (<*>), part.bind_eq_bind, part.bind_map, part.map_eq_map], congr, ext x, simp, tauto, }

private lemma time_frespects_once_eval_aux (f : code) (ih : ∀ v : ptree, (f.time v).dom ↔ (f.eval v).dom) :
  pfun.frespects_once (time_fix_fun f) (eval_fix_fun f) prod.fst :=
begin
  intro a, split,
  { simp [ih, time_fix_fun, eval_fix_fun], }, split,
  { intro a', simp [← apply_ite part.some, time_fix_fun, eval_fix_fun],
    rintros n hn e he h rfl, use [e, he, h], },
  simp [← apply_ite part.some, time_fix_fun, eval_fix_fun],
  rintros n₁ n₂ hn₂ b hb h rfl,
  use [b.right, b, hb, h],
end

lemma time_dom_iff_eval_dom (c : code) (v : ptree) : (c.time v).dom ↔ (c.eval v).dom :=
begin
  induction c generalizing v,
  all_goals { simp [code.time, add_def], },
  case code.node : c₁ c₂ c₁ih c₂ih { simp [c₁ih, c₂ih], },
  case code.comp : c₁ c₂ c₁ih c₂ih { simp [c₁ih, c₂ih], tauto, },
  case code.case : c₁ c₂ c₁ih c₂ih { simp [c₁ih, c₂ih], },
  case code.fix : f ih
  { apply pfun.eq_dom_of_frespects_once prod.fst,
    exact time_frespects_once_eval_aux f ih, }
end

lemma time_frespects_once_eval (f : code) : pfun.frespects_once (time_fix_fun f) (eval_fix_fun f) prod.fst :=
by { apply time_frespects_once_eval_aux, simp [time_dom_iff_eval_dom], }

def time_bound (c : code) (bound : ℕ → ℕ) : Prop :=
∀ (n : ℕ) (v : ptree), v.sizeof ≤ n → ∃ t ∈ c.time v, t ≤ bound n

lemma time_bound_of_time_bound_le {c : code} {b₁ : ℕ → ℕ} (hb₁ : time_bound c b₁) {b₂ : ℕ → ℕ} (hb₂ : ∀ n, b₁ n ≤ b₂ n) :
  time_bound c b₂ := λ n v hnv, by { obtain ⟨t, ht, hb⟩ := hb₁ n v hnv, use [t, ht, hb.trans (hb₂ n)], }

-- lemma eval_dom_univ_iff_exists_time_bound (c : code) : (∃ (b : ℕ → ℕ), time_bound c b) ↔ (∀ v, (c.eval v).dom) :=
-- ⟨λ ⟨b, hb⟩ v, by { rw [← time_dom_iff_eval_dom, part.dom_iff_mem], specialize hb v.sizeof _ rfl.le, tauto, },
--  λ h, by { simp only [← time_dom_iff_eval_dom] at h, sorry, /- needs: only finitely many trees of each size -/ }⟩

lemma eval_dom_of_time_bound {c : code} {bound : ℕ → ℕ} (h : time_bound c bound) : c.eval.dom = set.univ :=
begin
  ext v, 
  suffices : (c.time v).dom, { simpa [pfun.dom, time_dom_iff_eval_dom], },
  rw part.dom_iff_mem,
  specialize h v.sizeof _ rfl.le, tauto
end

lemma dom_univ_iff {α β : Type*} (f : α →. β) : f.dom = set.univ ↔ ∀ x, (f x).dom :=
by simp [pfun.dom, set.eq_univ_iff_forall]

def time_bound_of_monotonic_iff (c : code) {bound : ℕ → ℕ} (mono : monotone bound) :
  time_bound c bound ↔ ∀ v, ∃ t ∈ c.time v, t ≤ bound v.sizeof :=
begin
  split, { intros h v, exact h v.sizeof v rfl.le, },
  intros h n v hnv,
  rcases h v with ⟨t, H₁, H₂⟩,
  use [t, H₁, H₂.trans (mono hnv)],
end

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
    exact c₁ih H ht₂,  },
  case code.case : c₁ c₂ c₁ih c₂ih
  { simp [code.time] at hv ht,
    rcases ht with ⟨t', ht', rfl⟩,
    split_ifs at *, { linarith only [c₁ih hv ht'], }, { linarith only [c₂ih hv ht'], } },
  case code.fix : f ih
  { simp only [code_fix_eval] at hv, simp [code_fix_time, add_def] at ht,
    rcases ht with ⟨t, ht, rfl⟩,
    obtain ⟨⟨v', t'⟩, H₁, H₂⟩ := pfun.frespects_last_step (time_frespects_once_eval f) ht hv,
    simp [time_fix_fun, eval_fix_fun, ← apply_ite part.some] at H₁ H₂,
    rcases H₁ with ⟨lt, hlt, vout', hvout', hvout_left, rfl⟩,
    rcases H₂ with ⟨vout'', hvout'', hvout_left, rfl⟩,
    cases part.mem_unique hvout' hvout'',
    refine (ptree.right_sizeof_le _).trans _,
    linarith only [ih hvout' hlt], }
end

lemma time_bound_left : time_bound code.left id :=
by { rw time_bound_of_monotonic_iff _ monotone_id, simp [code.time], }

lemma time_bound_right : time_bound code.right id := time_bound_left

lemma time_bound_id : time_bound code.id id := time_bound_left

lemma time_bound_nil : time_bound code.nil (λ _, 1) :=
by { rw time_bound_of_monotonic_iff _ monotone_const, simp [code.time], }

lemma time_bound_node {c₁ c₂ : code} {b₁ b₂ : ℕ → ℕ} (hb₁ : time_bound c₁ b₁) (hb₂ : time_bound c₂ b₂) :
  time_bound (code.node c₁ c₂) (λ t, b₁ t + b₂ t + 1) :=
begin
  intros n v hnv,
  obtain ⟨t₁, ht₁, hb₁⟩ := hb₁ n v hnv,
  obtain ⟨t₂, ht₂, hb₂⟩ := hb₂ n v hnv,
  use t₁ + t₂ + 1, split,
  { rw ← part.eq_some_iff at ht₁ ht₂, simp [code.time, ht₁, ht₂, add_def], ring, },
  mono*,
end

lemma time_bound_comp {c₁ c₂ : code} {b₁ b₂ : ℕ → ℕ} (hb₁ : time_bound c₁ b₁) (hb₂ : time_bound c₂ b₂) :
  time_bound (c₁.comp c₂) (λ t, b₁ (b₂ t) + b₂ t + 1) :=
begin
  intros n v hnv,
  obtain ⟨t₂, ht₂, hb₂⟩ := hb₂ n v hnv,
  obtain ⟨v', hv'⟩ := (_ : ∃ v', v' ∈ c₂.eval v), swap,
  { rw [← part.dom_iff_mem, ← time_dom_iff_eval_dom, part.dom_iff_mem], use [t₂, ht₂], },
  obtain ⟨t₁, ht₁, hb₁⟩ := hb₁ (b₂ n) v' _,
  use t₁ + t₂ + 1, split,
  { rw ← part.eq_some_iff at ht₁ ht₂ hv', simp [code.time, ht₁, ht₂, hv', add_def], ring, },
  { mono*, },
  { exact (eval_sizeof_le_time hv' ht₂).trans hb₂, },
end

lemma time_bound_case {c₁ c₂ : code} {b₁ b₂ : ℕ → ℕ} (hb₁ : time_bound c₁ b₁) (hb₂ : time_bound c₂ b₂) :
  time_bound (code.case c₁ c₂) (λ t, max (b₁ t) (b₂ t) + 1) :=
begin
  intros n v hnv,
  specialize hb₁ n v.right ((ptree.right_sizeof_le _).trans hnv),
  specialize hb₂ n v.right ((ptree.right_sizeof_le _).trans hnv),
  simp [code.time], split_ifs,
  { obtain ⟨t, ht, H⟩ := hb₁, use [t, ht], left, exact H, },
  { obtain ⟨t, ht, H⟩ := hb₂, use [t, ht], right, exact H, },
end

lemma time_bound_case' {c₁ c₂ : code} {b₁ b₂ : ℕ → ℕ} (hb₁ : time_bound c₁ b₁) (hb₂ : time_bound c₂ b₂) :
  time_bound (code.case c₁ c₂) (λ t, (b₁ t) + (b₂ t) + 1) :=
by { apply time_bound_of_time_bound_le (time_bound_case hb₁ hb₂), intro, simp, }

