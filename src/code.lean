import data.pfun
import plain_tree
import succ_graphs

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
| (code.fix f) := λ x₀, execution.eval ⟨λ x, if x.left = ptree.nil then part.some none else (f.eval x).map some, x₀⟩

def code.fix_iterator (f : code) (x₀ : ptree) : execution ptree :=
⟨λ x, if x.left = ptree.nil then part.some none else (f.eval x).map some, x₀⟩

lemma code.eval_fix (f : code) (x : ptree) : f.fix.eval x = (f.fix_iterator x).eval := rfl
@[simp] lemma code.none_mem_eval_fix {f : code} {x x₀ : ptree} :
  none ∈ (f.fix_iterator x₀).next x ↔ x.left = ptree.nil :=
by { simp only [code.fix_iterator], split_ifs; simpa, }

@[simp] lemma code.some_mem_eval_fix {f : code} {x x₀ x' : ptree} :
  some x' ∈ (f.fix_iterator x₀).next x ↔ x.left ≠ ptree.nil ∧ x' ∈ f.eval x :=
by { simp only [code.fix_iterator], split_ifs; simp; tauto, }

@[simp] lemma code.fix_iterator_start (f : code) (x₀ : ptree) :
  (f.fix_iterator x₀).start = x₀ := rfl


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
