import data.set.basic
import logic.embedding
import pfun_to_fun
import polytime


def polydecidable_aux (P : ptree → Prop) : Prop :=
∃ (c : code) (pc : polytime c), ∀ x, ptree.nil ∈ c.eval x ↔ P x 

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

lemma mem_poly (α : Type*) [polycodable α] : polydecidable (∈ set.range (@encode α _)) := polycodable.mem_poly'

def polytime_fun {α β : Type*} [polycodable α] [polycodable β] (f : α → β) :=
∃ (c : code) (pc : polytime c), ∀ x, c.eval (encode x) = part.some (encode (f x))

section polytime_fun

@[elab_as_eliminator]
lemma polydecidable_of_preimage_polytime {f : β → α} (P : α → Prop)  :
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

lemma polydecidable.children {P₁ P₂ : ptree → Prop} (h₁ : polydecidable P₁) (h₂ : polydecidable P₂) :
  polydecidable (λ x, x ≠ ptree.nil ∧ P₁ x.left ∧ P₂ x.right) :=
begin
  apply polydecidable.and, apply polydecidable.not eq_nil_aux, apply polydecidable.and,
  exact polydecidable_of_preimage_polytime _ polytime_fun.ptree_left h₁,
  exact polydecidable_of_preimage_polytime _ polytime_fun.ptree_right h₂,
end

private lemma eq_const_aux : ∀ (x : ptree), polydecidable (=x)
| ptree.nil := eq_nil_aux
| (ptree.node a b) :=
begin
  convert_to polydecidable (λ x, x ≠ ptree.nil ∧ x.left = a ∧ x.right = b),
  { ext x, cases x; simp, },
  exact polydecidable.children (eq_const_aux a) (eq_const_aux b),
end

lemma polydecidable.eq_const (x : α) : polydecidable (=x) :=
let ⟨c, pc, s⟩ := eq_const_aux (encode x) in ⟨c, pc, λ x', by simpa using s (encode x')⟩

section pair

instance : polycodable (α × β) :=
{ encode := ⟨λ x, ptree.node (encode x.1) (encode x.2), λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩, by simpa using and.intro⟩,
  mem_poly' :=
begin
  convert_to polydecidable (λ x, x ≠ ptree.nil ∧ x.left ∈ set.range (@encode α _) ∧ x.right ∈ set.range (@encode β _)),
  { ext x, split,
    { rintro ⟨y, hy⟩, simp at hy, subst hy, simp, }, 
    rintro ⟨nnil, ⟨ly, hly⟩, ⟨ry, hry⟩⟩,
    have : x = ptree.node (encode ly) (encode ry), { cases x, contradiction, simp [hly, hry], }, subst this,
    use (ly, ry), simp, },
  exact polydecidable.children (mem_poly α) (mem_poly β)
end }

lemma polytime_fun.prod_fst : polytime_fun (@prod.fst α β) :=
⟨code.left, polytime_left, λ ⟨a, b⟩, by { simp, refl, }⟩

lemma polytime_fun.prod_snd : polytime_fun (@prod.snd α β) :=
⟨code.right, polytime_left, λ ⟨a, b⟩, by { simp, refl, }⟩

lemma polytime_fun.pair {f : α → β} {g : α → γ} : polytime_fun f → polytime_fun g → polytime_fun (λ x, (f x, g x))
| ⟨c₁, pc₁, s₁⟩ ⟨c₂, pc₂, s₂⟩ := ⟨code.node c₁ c₂, polytime_node pc₁ pc₂, λ x, by { simp [s₁, s₂], refl, }⟩

def polytime_fun₂ (f : α → β → γ) : Prop := polytime_fun (function.uncurry f)

lemma is_polytime₂_comp {δ : Type*} [polycodable δ] {f : α → β → γ} {g : δ → α} {h : δ → β} 
  (hf : polytime_fun₂ f) (hg : polytime_fun g) (hh : polytime_fun h) :
  polytime_fun (λ x, f (g x) (h x)) :=
polytime_fun.comp hf (polytime_fun.pair hg hh)

end pair

section bool

instance : polycodable bool :=
{ encode := ⟨λ b, cond b ptree.nil (ptree.node ptree.nil ptree.nil), 
begin
  rw function.injective_iff_has_left_inverse,
  use (=ptree.nil), intro b, cases b; simp,
end⟩,
  mem_poly' :=
begin
  rw polydecidable_aux_iff,
  convert_to polydecidable (λ x, x = ptree.nil ∨ x = ptree.node ptree.nil ptree.nil),
  { ext v, split, { rintro ⟨b, hb⟩, cases b; simp at hb; tauto, },
    rintro (rfl|rfl), { use tt, simp, }, { use ff, simp, } },
  apply polydecidable.or; apply polydecidable.eq_const _,
end }

lemma polydecidable_iff_polytime_fun (P : α → Prop) [decidable_pred P] :
  polydecidable P ↔ polytime_fun (λ x, (P x : bool)) :=
begin
  split,
  { intro h, change polytime_fun (λ x, if P x then tt else ff),
    apply polytime_fun.ite h; apply polytime_fun.const _, },
  { intro h, convert_to polydecidable (λ x, (P x : bool) = tt),
    { ext x, simp, }, 
    apply polydecidable_of_preimage_polytime (=tt) h,
    apply polydecidable.eq_const _, }
end

end bool

section list



end list

end polytime_fun

