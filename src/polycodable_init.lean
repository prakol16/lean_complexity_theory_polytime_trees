import data.set.basic
import logic.embedding
import pfun_to_fun
import polytime

class polycodable (α : Type*) :=
(encode : α → ptree)
(decode : ptree → α)
(decode_encode : ∀ x, decode (encode x) = x)
(polytime_decode [] : ∃ (c : code) (pc : polytime c), ∀ x, c.eval x = part.some (encode (decode x)))

attribute [simp, higher_order] polycodable.decode_encode

open polycodable (encode decode)

def polytime_fun {α β : Type*} [polycodable α] [polycodable β] (f : α → β) :=
∃ (c : code) (pc : polytime c), ∀ x, c.eval (encode x) = part.some (encode (f x))

instance : polycodable ptree :=
{ encode := id,
  decode := id,
  decode_encode := λ _, rfl,
  polytime_decode := ⟨_, polytime_id, λ x, by simp⟩ }

@[simp] lemma ptree_encode (p : ptree) : encode p = p := rfl

variables {α β γ : Type*} [polycodable α] [polycodable β] [polycodable γ]

lemma polytime_fun_iff' (f : ptree → ptree) :
  (∃ (c : code) (pc : polytime c), ∀ x, c.eval x = part.some (f x)) ↔ polytime_fun f := iff.rfl

lemma polytime_fun_iff (f : α → β) :
  polytime_fun f ↔ ∃ (c : code) (pc : polytime c), ∀ x, c.eval x = part.some (encode (f (decode x))) :=
begin
  split,
  { rintro ⟨c, pc, s⟩, rcases polycodable.polytime_decode α with ⟨c₂, pc₂, s₂⟩,
    use [c.comp c₂, polytime_comp pc pc₂], intro x, simp [s₂, s], },
  rintro ⟨c, pc, s⟩, use [c, pc], intro x, simp [s],
end

lemma polytime_fun_iff'' (f : α → β) :
  polytime_fun f ↔ ∃ (c : code) (pc : polytime c), ∀ x, (c.eval (encode x)).map decode = part.some (f x) :=
begin
  split, { rintro ⟨c, pc, s⟩, use [c, pc], simp [s], },
  rintro ⟨c, pc, s⟩, rcases polycodable.polytime_decode β with ⟨c₂, pc₂, s₂⟩,
  use [c₂.comp c, polytime_comp pc₂ pc], intro x, specialize s x,
  simp [part.eq_some_iff] at s ⊢, rcases s with ⟨a, h₁, h₂⟩, use [a, h₁],
  simp [s₂, h₂],
end

lemma polytime_fun.encode : polytime_fun (@encode α _) :=
⟨code.id, polytime_id, λ x, by simp⟩

lemma polytime_fun.decode {f : α → β} (hf : polytime_fun (encode ∘ f)) : polytime_fun f := hf

lemma polytime_fun.decode' : polytime_fun (@decode α _) :=
by { rw polytime_fun_iff, exact polycodable.polytime_decode _, }

lemma polytime_fun.id : polytime_fun (@id α) := ⟨code.id, polytime_id, λ x, by simp⟩

lemma polytime_fun.const (x : α) : polytime_fun (function.const β x) := ⟨code.const (encode x), polytime_const _, λ x, by simp⟩

lemma polytime_fun.comp {f : β → γ} {g : α → β} : polytime_fun f → polytime_fun g → polytime_fun (f ∘ g)
| ⟨c₁, pc₁, s₁⟩ ⟨c₂, pc₂, s₂⟩ := ⟨c₁.comp c₂, polytime_comp pc₁ pc₂, λ x, by simp [s₁, s₂]⟩

lemma polytime_fun.ptree_left : polytime_fun ptree.left := ⟨code.left, polytime_left, λ x, by simp⟩
lemma polytime_fun.ptree_right : polytime_fun ptree.right := ⟨code.right, polytime_right, λ x, by simp⟩

lemma polycodable.encode_injective (α : Type*) [polycodable α] : function.injective (@encode α _) :=
λ x y hxy, by { apply_fun (@decode α _) at hxy, simpa using hxy, }

@[simp] lemma polycodable.encode_inj_iff {x y : α} : encode x = encode y ↔ x = y :=
(polycodable.encode_injective α).eq_iff

lemma polytime_fun.polytime_code {c : code} (pc : polytime c) : polytime_fun pc.to_fun := ⟨c, pc, λ x, by simp⟩

section pair

private lemma polytime_fun.node {f : ptree → ptree} {g : ptree → ptree} : polytime_fun f → polytime_fun g → polytime_fun (λ x, (f x).node (g x))
| ⟨cf, pf, sf⟩ ⟨cg, pg, sg⟩ := ⟨cf.node cg, polytime_node pf pg, λ x, by { simp at sf sg, simp [sf, sg], }⟩ 

instance : polycodable (α × β) :=
{ encode := λ x, ptree.node (encode x.1) (encode x.2),
  decode := λ v, (decode v.left, decode v.right),
  decode_encode := λ x, by simp,
  polytime_decode :=
begin
  rw polytime_fun_iff', apply polytime_fun.node; dsimp only,
  { apply polytime_fun.comp polytime_fun.encode, apply polytime_fun.comp polytime_fun.decode' polytime_fun.ptree_left, },
  { apply polytime_fun.comp polytime_fun.encode, apply polytime_fun.comp polytime_fun.decode' polytime_fun.ptree_right, },
end }

variables {δ : Type*} [polycodable δ]
lemma polytime_fun.fst : polytime_fun (@prod.fst α β) :=
⟨code.left, polytime_left, λ ⟨a, b⟩, by { simp, refl, }⟩

lemma polytime_fun.snd : polytime_fun (@prod.snd α β) :=
⟨code.right, polytime_left, λ ⟨a, b⟩, by { simp, refl, }⟩

lemma polytime_fun.pair {f : α → β} {g : α → γ} : polytime_fun f → polytime_fun g → polytime_fun (λ x, (f x, g x))
| ⟨c₁, pc₁, s₁⟩ ⟨c₂, pc₂, s₂⟩ := ⟨code.node c₁ c₂, polytime_node pc₁ pc₂, λ x, by { simp [s₁, s₂], refl, }⟩

def polytime_fun₂ (f : α → β → γ) : Prop := polytime_fun (function.uncurry f)

def polytime_fun₃ {δ : Type*} [polycodable δ] (f : α → β → γ → δ) : Prop :=
polytime_fun (λ x : α × β × γ, f x.1 x.2.1 x.2.2)

lemma polytime_fun.comp₂ {δ : Type*} [polycodable δ] {f : α → β → γ} {g : δ → α} {h : δ → β} 
  (hf : polytime_fun₂ f) (hg : polytime_fun g) (hh : polytime_fun h) :
  polytime_fun (λ x, f (g x) (h x)) :=
polytime_fun.comp hf (polytime_fun.pair hg hh)

lemma polytime_fun.comp₃ {δ ε : Type*} [polycodable δ] [polycodable ε] {f : α → β → γ → δ} {g₁ : ε → α} {g₂ : ε → β} {g₃ : ε -> γ} 
  (hf : polytime_fun₃ f) (hg₁ : polytime_fun g₁) (hg₂ : polytime_fun g₂) (hg₃ : polytime_fun g₃) :
  polytime_fun (λ x, f (g₁ x) (g₂ x) (g₃ x)) :=
polytime_fun.comp hf (polytime_fun.pair hg₁ (polytime_fun.pair hg₂ hg₃))

lemma polytime_fun.node : polytime_fun₂ ptree.node := polytime_fun.id

end pair
