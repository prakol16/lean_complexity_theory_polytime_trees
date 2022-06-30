import data.set.basic
import logic.embedding
import pfun_to_fun
import polytime


def polydecidable_aux (P : ptree → Prop) : Prop :=
∃ (c : code) (pc : polytime c), ∀ x, ptree.nil ∈ c.eval x ↔ P x 

-- lemma polydecidable_code_eval_nil_iff (P : ptree → Prop) [h : polydecidable P] (x : ptree) :
--   (h.c.eval.to_fun h.pc.dom_univ x = ptree.nil) ↔ P x :=
-- by { unfreezingI { cases h with c pc sound }, rw ← sound x, exact part.get_eq_iff_mem _, }

-- def decidable_of_polydecidable (P : ptree → Prop) [polydecidable P] : decidable_pred P :=
-- by { intro x, rw ← polydecidable_code_eval_nil_iff P x, apply_instance, }

-- private lemma no_confusion_ite_ptree (c : Prop) [decidable c] (a b : ptree) (z : part ptree) :
--   ptree.nil ∈ (if c then z else (part.some $ ptree.node a b)) ↔ c ∧ ptree.nil ∈ z :=
-- by split_ifs; simp [h]

-- private lemma no_confusion_ite_ptree' (c : Prop) [decidable c] (a b : ptree) (z : part ptree) :
--   ptree.nil ∈ (if c then (part.some $ ptree.node a b) else z) ↔ ¬c ∧ ptree.nil ∈ z :=
-- by split_ifs; simp [h]

-- private lemma no_confusion_ite_ptree'' (c : Prop) [decidable c] (a b : ptree) :
--   ptree.nil = (if c then (ptree.node a b) else ptree.nil) ↔ ¬c :=
-- by split_ifs; simp [h]

-- private lemma no_confusion_ite_ptree''' (c : Prop) [decidable c] (a b : ptree) :
--   ptree.nil = (if c then ptree.nil else (ptree.node a b)) ↔ c :=
-- by split_ifs; simp [h]

-- instance polydecidable_true : polydecidable (λ _, true) :=
-- ⟨code.nil, polytime_nil, λ x, by simp⟩

-- instance polydecidable_false : polydecidable (λ _, false) :=
-- ⟨code.const (ptree.node ptree.nil ptree.nil), polytime_const _, λ _, by simp⟩

-- instance polydecidable_and (P₁ P₂ : ptree → Prop) [h₁ : polydecidable P₁] [h₂ : polydecidable P₂] :
--   polydecidable (λ x, P₁ x ∧ P₂ x) :=
-- begin
--   unfreezingI { cases h₁ with c₁ pc₁ sound₁, cases h₂ with c₂ pc₂ sound₂, },
--   use code.ite c₁ c₂ (code.const $ ptree.node ptree.nil ptree.nil),
--   { apply polytime_ite pc₁ pc₂, apply polytime_const, },
--   intro x, simp [no_confusion_ite_ptree, sound₁, sound₂],
--   split, { rintro ⟨nil', h₁, rfl, h₂⟩, rw sound₁ at h₁, exact ⟨h₁, h₂⟩, },
--   { rintro ⟨h₁, h₂⟩, use ptree.nil, simp [sound₁, h₁, h₂], }
-- end

-- instance polydecidable_not (P : ptree → Prop) [h : polydecidable P] :
--   polydecidable (λ x, ¬P x) :=
-- begin
--   unfreezingI { cases h with c pc sound, },
--   use code.ite c (code.const $ ptree.node ptree.nil ptree.nil) code.nil,
--   { apply polytime_ite pc (polytime_const _) polytime_nil, },
--   intro x, simp [← apply_ite part.some, no_confusion_ite_ptree''],
--   split, { rintro ⟨v, hv, hv'⟩ p, rw ← sound at p, cases part.mem_unique hv p, contradiction, },
--   { intro h, rw ← sound at h,
--     obtain ⟨a, ha⟩ := (_ : ∃ a, a ∈ c.eval x), swap,
--     { rw ← part.dom_iff_mem, change x ∈ c.eval.dom, rw pc.dom_univ, trivial, },
--     use [a, ha], rintro ⟨rfl⟩, contradiction, }
-- end

-- instance polydecidable_or (P₁ P₂ : ptree → Prop) [polydecidable P₁] [polydecidable P₂] :
--   polydecidable (λ x, P₁ x ∨ P₂ x) :=
-- by { simp only [or_iff_not_and_not], apply_instance, }

-- def polydecidable_eq_nil : polydecidable (=ptree.nil) :=
-- ⟨code.id, polytime_id, λ x, by { simp, exact comm, }⟩

class polycodable (α : Type*) :=
(encode : α ↪ ptree)
(mem_poly' : polydecidable_aux (∈ set.range encode))

open polycodable (encode)

instance : polycodable ptree :=
{ encode := function.embedding.refl _,
  mem_poly' := ⟨code.nil, polytime_nil, by simp⟩ }

@[simp] lemma ptree_encode (p : ptree) : encode p = p := rfl

variables {α β γ : Type*} [polycodable α] [polycodable β] [polycodable γ]

def polydecidable (P : α → Prop) : Prop :=
∃ (c : code) (pc : polytime c), ∀ x, ptree.nil ∈ c.eval (encode x) ↔ P x   

@[simp] lemma polydecidable_aux_iff (P : ptree → Prop) : polydecidable_aux P ↔ polydecidable P :=
⟨λ ⟨c, pc, sound⟩, ⟨c, pc, sound⟩, λ ⟨c, pc, sound⟩, ⟨c, pc, sound⟩⟩

def polytime_fun {α β : Type*} [polycodable α] [polycodable β] (f : α → β) :=
∃ (c : code) (pc : polytime c), ∀ x, c.eval (encode x) = part.some (encode (f x))

section polytime_fun

lemma polydecidable_of_preimage_polytime {f : β → α} {P : α → Prop}  :
  polytime_fun f → polydecidable P → polydecidable (λ y, P (f y))
| ⟨c₁, pc₁, sound₁⟩ ⟨c₂, pc₂, sound₂⟩ := ⟨c₂.comp c₁, polytime_comp pc₂ pc₁, λ y, by simp [sound₁, sound₂]⟩

lemma polytime_fun.id : polytime_fun (@id α) := ⟨code.id, polytime_id, λ x, by simp⟩

lemma polytime_fun.const (x : α) : polytime_fun (function.const β x) := ⟨code.const (encode x), polytime_const _, λ x, by simp⟩

lemma polytime_fun.comp {f : β → γ} {g : α → β} : polytime_fun f → polytime_fun g → polytime_fun (f ∘ g)
| ⟨c₁, pc₁, s₁⟩ ⟨c₂, pc₂, s₂⟩ := ⟨c₁.comp c₂, polytime_comp pc₁ pc₂, λ x, by simp [s₁, s₂]⟩

lemma polytime_fun.ptree_left : polytime_fun ptree.left := ⟨code.left, polytime_left, λ x, by simp⟩
lemma polytime_fun.ptree_right : polytime_fun ptree.right := ⟨code.right, polytime_right, λ x, by simp⟩

protected lemma polytime_fun.ite {c : α → Prop} [decidable_pred c] {t : α → β} {f : α → β} :
  polydecidable c → polytime_fun t → polytime_fun f → polytime_fun (λ x, if c x then t x else f x)
| ⟨c₁, pc₁, s₁⟩ ⟨c₂, pc₂, s₂⟩ ⟨c₃, pc₃, s₃⟩ :=
⟨code.ite c₁ c₂ c₃, polytime_ite pc₁ pc₂ pc₃, λ x, 
begin
  specialize s₁ x, specialize s₂ x, specialize s₃ x,
  by_cases h : c x,
  { simp only [h, iff_true, ← part.eq_some_iff] at s₁, simp [h, s₁, s₂], },
  { simp only [h, iff_false] at s₁,
    obtain ⟨v, hv⟩ := (_ : ∃ v, v ∈ c₁.eval (encode x)),
    have : v ≠ ptree.nil := by { rintro rfl, contradiction, },
    { rw ← part.eq_some_iff at hv, simp [h, hv, this, s₃], },
    rw ← part.dom_iff_mem, exact pc₁.dom_univ' _, }
end⟩

lemma polydecidable.or {P₁ P₂ : α → Prop} : polydecidable P₁ → polydecidable P₂ → polydecidable (λ x, (P₁ x) ∨ (P₂ x)) :=
begin
  classical,
  rintros h₁ ⟨c₂, pc₂, s₂⟩,
  suffices : polytime_fun (λ x, if P₁ x then ptree.nil else c₂.eval.to_fun pc₂.dom_univ (encode x)),
  { rcases this with ⟨c, pc, s⟩, use [c, pc], intro x,
    by_cases h : P₁ x, { simp [s, h], },
    simp [s, h, pfun.to_fun, s₂], },
  apply polytime_fun.ite h₁ (polytime_fun.const _) ⟨c₂, pc₂, _⟩,
  intro x, simp [pfun.to_fun],
end

lemma polydecidable.not {P : α → Prop} (h : polydecidable P) : polydecidable (λ x, ¬P x) :=
begin
  classical,
  suffices : polytime_fun (λ x, if P x then ptree.node ptree.nil ptree.nil else ptree.nil),
  { rcases this with ⟨c, pc, s⟩, use [c, pc], intro x, simp [s x], split_ifs; simpa, },
  apply polytime_fun.ite h (polytime_fun.const _) (polytime_fun.const _),
end

lemma polydecidable.and {P₁ P₂ : α → Prop} (h₁ : polydecidable P₁) (h₂ : polydecidable P₂) : polydecidable (λ x, (P₁ x) ∧ (P₂ x)) :=
begin
  simp only [and_iff_not_or_not],
  apply polydecidable.not, apply polydecidable.or; apply polydecidable.not; assumption,
end

private lemma eq_nil_aux : polydecidable (=ptree.nil) := ⟨code.id, polytime_id, λ x, by { simp, exact comm, }⟩
private lemma eq_const_aux : ∀ (x : ptree), polydecidable (=x)
| ptree.nil := eq_nil_aux
| (ptree.node a b) :=
begin
  convert_to polydecidable (λ x, x ≠ ptree.nil ∧ x.left = a ∧ x.right = b),
  { ext x, cases x; simp, },
  apply polydecidable.and, apply polydecidable.not eq_nil_aux, apply polydecidable.and,
  exact polydecidable_of_preimage_polytime polytime_fun.ptree_left (eq_const_aux a),
  exact polydecidable_of_preimage_polytime polytime_fun.ptree_right (eq_const_aux b),
end

lemma polydecidable.eq_const (x : α) : polydecidable (=x) :=
let ⟨c, pc, s⟩ := eq_const_aux (encode x) in ⟨c, pc, λ x', by simpa using s (encode x')⟩



end polytime_fun

