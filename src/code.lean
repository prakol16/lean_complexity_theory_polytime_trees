import data.pfun
import plain_tree
import reaches

open part_eval

inductive code
| left : code
| right : code
| nil : code
| id : code
| node : code → code → code
| comp : code → code → code
| case : code → code → code
| fix : code → code

@[simp] def code.eval : code → ptree →. ptree
| code.left := λ t, part.some t.left
| code.right := λ t, part.some t.right
| code.nil := λ _, part.some ptree.nil
| code.id := λ t, part.some t
| (code.node l r) := λ t, do x ← l.eval t, y ← r.eval t, part.some (ptree.node x y)
| (code.comp f g) := λ t, g.eval t >>= f.eval
| (code.case f g) := λ t, if t.left = ptree.nil then f.eval t.right else g.eval t.right
| (code.fix f) := eval (λ t : ptree, (f.eval t).map ptree.to_option)

local infixr `∘`:90 := code.comp

protected def code.const : ptree → code
| ptree.nil := code.nil
| (ptree.node l r) := code.node (code.const l) (code.const r)

@[simp] lemma const_eval (t : ptree) : (code.const t).eval = λ _, t :=
by { ext : 1, induction t with l r ihl ihr, { simp [code.const], }, simp [code.const, ihl, ihr], }

protected def code.ite (cond : code) (t : code) (f : code) : code :=
(code.case t f) ∘ (code.node cond code.id)

@[simp] lemma ite_eval (cond : code) (t : code) (f : code) (v : ptree) :
  (code.ite cond t f).eval v = (cond.eval v) >>= λ v', if v' = ptree.nil then t.eval v else f.eval v :=
begin
  simp only [code.ite, code.eval],
  by_cases h : cond.eval v = part.none, { rw h, simp, },
  simp only [part.eq_none_iff, not_forall, not_not] at h,
  rcases h with ⟨x, h⟩, rw ← part.eq_some_iff at h, rw h,
  simp,
end

lemma ite_dom (cond : code) (t : code) (f : code) (x : ptree) :
  ((cond.ite t f).eval x).dom ↔ ∃ r : ptree, r ∈ cond.eval x ∧
    (r = ptree.nil → (t.eval x).dom) ∧
    (r ≠ ptree.nil → (f.eval x).dom) :=
begin
  by_cases (cond.eval x).dom, swap,
  { simp [h], intros _ H, exfalso, exact h (part.dom_iff_mem.mpr ⟨_, H⟩), },
  rw part.dom_iff_mem at h, cases h with r hr,
  split,
  { intro h, use [r, hr], 
    rw ← part.eq_some_iff at hr,
    simp [hr] at h,
    split_ifs at h; tauto, },
  rintro ⟨r', hr', H₁, H₂⟩, cases part.mem_unique hr hr',
  rw ← part.eq_some_iff at hr,
  simp [hr], split_ifs; tauto,
end