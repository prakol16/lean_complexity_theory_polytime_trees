import data.set.basic
import logic.embedding
import pfun_to_fun
import polytime

open ptree (pencodable)
open ptree.pencodable (encode decode)

def polytime_fun {α β : Type*} [pencodable α] [pencodable β] (f : α → β) :=
∃ (c : code) (pc : polytime c), ∀ x, c.eval (encode x) = part.some (encode (f x))

section
variables {α β γ δ ε : Type*} [pencodable α] [pencodable β] [pencodable γ]
  [pencodable δ] [pencodable ε]

lemma polytime_fun.encode {α : Type*} [pencodable α] : polytime_fun (@encode α _) :=
⟨code.id, polytime_id, λ x, by simp⟩

lemma polytime_fun.decode {f : α → β} (hf : polytime_fun (encode ∘ f)) : polytime_fun f := hf

lemma polytime_fun.id : polytime_fun (@id α) := ⟨code.id, polytime_id, λ x, by simp⟩

lemma polytime_fun.const (x : α) : polytime_fun (function.const β x) := ⟨code.const (encode x), polytime_const _, λ x, by simp⟩

lemma polytime_fun.comp {f : β → γ} {g : α → β} : polytime_fun f → polytime_fun g → polytime_fun (f ∘ g)
| ⟨c₁, pc₁, s₁⟩ ⟨c₂, pc₂, s₂⟩ := ⟨c₁.comp c₂, polytime_comp pc₁ pc₂, λ x, by simp [s₁, s₂]⟩


section pair

lemma polytime_fun.fst : polytime_fun (@prod.fst α β) :=
⟨code.left, polytime_left, λ ⟨a, b⟩, by simp [ptree.pencodable.encode_pair_def]⟩

lemma polytime_fun.snd : polytime_fun (@prod.snd α β) :=
⟨code.right, polytime_left, λ ⟨a, b⟩, by simp [ptree.pencodable.encode_pair_def]⟩

lemma polytime_fun.pair {f : α → β} {g : α → γ} : polytime_fun f → polytime_fun g → polytime_fun (λ x, (f x, g x))
| ⟨c₁, pc₁, s₁⟩ ⟨c₂, pc₂, s₂⟩ := ⟨code.node c₁ c₂, polytime_node pc₁ pc₂, λ x, by { simp [s₁, s₂], refl, }⟩

def polytime_fun₂ (f : α → β → γ) : Prop := polytime_fun (function.uncurry f)

def polytime_fun₃ (f : α → β → γ → δ) : Prop :=
polytime_fun (λ x : α × β × γ, f x.1 x.2.1 x.2.2)

lemma polytime_fun.comp₂ {f : α → β → γ} {g : δ → α} {h : δ → β} 
  (hf : polytime_fun₂ f) (hg : polytime_fun g) (hh : polytime_fun h) :
  polytime_fun (λ x, f (g x) (h x)) :=
polytime_fun.comp hf (polytime_fun.pair hg hh)

lemma polytime_fun.comp₃ {f : α → β → γ → δ} {g₁ : ε → α} {g₂ : ε → β} {g₃ : ε -> γ} 
  (hf : polytime_fun₃ f) (hg₁ : polytime_fun g₁) (hg₂ : polytime_fun g₂) (hg₃ : polytime_fun g₃) :
  polytime_fun (λ x, f (g₁ x) (g₂ x) (g₃ x)) :=
polytime_fun.comp hf (polytime_fun.pair hg₁ (polytime_fun.pair hg₂ hg₃))

end pair

end

class polycodable (α : Type*) extends ptree.pencodable α :=
(polytime_decode [] : polytime_fun (λ x : ptree, encode (decode x)))

instance : polycodable ptree :=
{ polytime_decode := ⟨_, polytime_id, λ x, by simp⟩ }

variables {α β γ : Type*} [polycodable α] [polycodable β] [polycodable γ]

lemma polytime_fun_iff (f : α → β) :
  polytime_fun f ↔ ∃ (c : code) (pc : polytime c), ∀ x, c.eval x = part.some (encode (f (decode x))) :=
begin
  split,
  { rintro ⟨c, pc, s⟩, rcases polycodable.polytime_decode α with ⟨c₂, pc₂, s₂⟩,
    use [c.comp c₂, polytime_comp pc pc₂], intro x, simp at s₂, simp [s₂, s], },
  rintro ⟨c, pc, s⟩, use [c, pc], intro x, simp [s],
end

lemma polytime_fun_iff' (f : α → β) :
  polytime_fun f ↔ ∃ (c : code) (pc : polytime c), ∀ x, (c.eval (encode x)).map decode = part.some (f x) :=
begin
  split, { rintro ⟨c, pc, s⟩, use [c, pc], simp [s], },
  rintro ⟨c, pc, s⟩, rcases polycodable.polytime_decode β with ⟨c₂, pc₂, s₂⟩,
  use [c₂.comp c, polytime_comp pc₂ pc], intro x, specialize s x,
  simp [part.eq_some_iff] at s ⊢, rcases s with ⟨a, h₁, h₂⟩, use [a, h₁],
  simp at s₂, simp [s₂, h₂],
end

lemma polytime_fun.decode' : polytime_fun (@decode α _) :=
by { rw polytime_fun_iff, exact polycodable.polytime_decode _, }

lemma polytime_fun.ptree_left : polytime_fun ptree.left := ⟨code.left, polytime_left, λ x, by simp⟩
lemma polytime_fun.ptree_right : polytime_fun ptree.right := ⟨code.right, polytime_right, λ x, by simp⟩

lemma polytime_fun.polytime_code {c : code} (pc : polytime c) : polytime_fun pc.to_fun := ⟨c, pc, λ x, by simp⟩

private lemma polytime_fun.node_aux {f : ptree → ptree} {g : ptree → ptree} : polytime_fun f → polytime_fun g → polytime_fun (λ x, (f x).node (g x))
| ⟨cf, pf, sf⟩ ⟨cg, pg, sg⟩ := ⟨cf.node cg, polytime_node pf pg, λ x, by { simp at sf sg, simp [sf, sg], }⟩ 

instance : polycodable (α × β) :=
{ polytime_decode :=
begin
  simp only [ptree.pencodable.decode_pair_def, ptree.pencodable.encode_pair_def],
  apply polytime_fun.node_aux,
  all_goals { apply polytime_fun.comp polytime_fun.encode, apply polytime_fun.comp polytime_fun.decode', },
  exacts [polytime_fun.ptree_left, polytime_fun.ptree_right],
end }

lemma polytime_fun.node : polytime_fun₂ ptree.node := polytime_fun.id
