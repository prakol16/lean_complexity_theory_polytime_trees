import data.set.basic
import logic.embedding
import pfun_to_fun
import polytime


structure polydecidable_aux (P : ptree → Prop) :=
(c : code)
(pc : polytime c)
(sound : ∀ x, ptree.nil ∈ c.eval x ↔ P x)

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
(mem_poly : polydecidable_aux (∈ set.range encode))

-- class polydecidable {α : Type*} (P : α → Prop) : 

open polycodable

instance : polycodable ptree :=
⟨function.embedding.refl _, by { simp, apply_instance, }⟩

@[simp] lemma range_of_surjective_comp {α β γ : Type*} (f : α → β) (g : β → γ) (hf : function.surjective f) :
  set.range (g ∘ f) = set.range g :=
begin
  ext y, split, { rintro ⟨x, hx⟩, use f x, exact hx, },
  rintro ⟨x', rfl⟩,
  obtain ⟨x, rfl⟩ := hf x',
  use x,
end


def polycodable_of_equiv {α β : Type*} [polycodable α] (h : α ≃ β) : polycodable β :=
⟨h.symm.to_embedding.trans encode, 
begin
  simp only [function.embedding.trans, function.embedding.coe_fn_mk, function.comp_app, equiv.to_embedding_apply],
  rw range_of_surjective_comp, { apply_instance, }, { exact h.symm.surjective, },
end⟩

structure polytime_fun {α β : Type*} [polycodable α] [polycodable β] (f : α → β) :=
(c : code)
(pc : polytime c)
(sound : ∀ x : α, c.eval (encode x) = part.some (encode (f x)))

section polytime_fun
variables {α β : Type*} [polycodable α] [polycodable β]

-- lemma polydecidable_of_preimage_polytime {f : β → α} (hf : polytime_fun f) (P : α → Prop) [h : polydecidable P]

end polytime_fun

instance (α β : Type*) [polycodable α] [polycodable β] : polycodable (α × β) :=
⟨⟨λ x, ptree.node (encode x.1) (encode x.2), λ x y, by { simp only [prod.ext_iff, embedding_like.apply_eq_iff_eq, and_imp], exact and.intro, }⟩, 
begin
  convert_to polydecidable (λ x, ¬(x = ptree.nil)), swap,
  { haveI := polydecidable_eq_nil, apply_instance, },
  ext x, simp only [set.mem_range, function.embedding.coe_fn_mk, prod.exists], split, { rintro ⟨a, b, rfl⟩, simp, },
  cases x with a b, { intro, contradiction, }, intro _,
end⟩
