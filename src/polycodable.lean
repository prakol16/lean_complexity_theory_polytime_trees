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

section bool

instance : polycodable bool :=
{ encode := λ b, cond b ptree.nil ptree.non_nil,
  decode := λ v, if v = ptree.nil then tt else ff,
  decode_encode := λ b, by cases b; simp,
  polytime_decode := ⟨_, 
  (polytime_ite polytime_id polytime_nil (polytime_const ptree.non_nil)), λ x, by cases x; simp [ptree.of_option]⟩ }

lemma polytime_fun.ite' {f : α → bool} {g h : α → β} : polytime_fun f → polytime_fun g → polytime_fun h → polytime_fun (λ x, cond (f x) (g x) (h x))
| ⟨cf, pf, sf⟩ ⟨cg, pg, sg⟩ ⟨ch, ph, sh⟩ :=
⟨code.ite cf cg ch, polytime_ite pf pg ph, λ x, by cases H : (f x); simp [sf, sg, sh, ← apply_ite part.some, ← apply_ite encode, encode, H]⟩ 

lemma polytime_fun.ite {P : α → Prop} [decidable_pred P] {g h : α → β} (hP : polytime_fun (λ x, (P x : bool))) (hg : polytime_fun g) (hh : polytime_fun h) :
  polytime_fun (λ x, if P x then g x else h x) :=
begin
  convert_to polytime_fun (λ x, cond (P x) (g x) (h x)),
  { ext x, by_cases P x; simp, },
  exact polytime_fun.ite' hP hg hh,
end


private lemma polytime_fun.eq_nil_aux : polytime_fun (λ x', (x' = ptree.nil : bool)) :=
⟨_, polytime_ite polytime_id polytime_nil (polytime_const ptree.non_nil), λ x, by cases x; simp [encode]⟩

lemma band_eq_cond (x y : bool) : x && y = cond x y ff := by cases x; simp

lemma ptree_children {f g : ptree → bool} (hf : polytime_fun f) (hg : polytime_fun g) :
  polytime_fun (λ x : ptree, (x ≠ ptree.nil) && (f x.left && g x.right)) :=
begin
  simp only [band_eq_cond, bool.to_bool_not, bool.cond_bnot, bool.cond_to_bool],
  apply polytime_fun.ite polytime_fun.eq_nil_aux, apply polytime_fun.const,
  refine polytime_fun.ite' _ _ (polytime_fun.const ff), apply polytime_fun.comp hf polytime_fun.ptree_left, apply polytime_fun.comp hg polytime_fun.ptree_right,
end

private lemma polytime_fun.eq_const_aux : ∀ (x : ptree), polytime_fun (λ x', (x' = x : bool))
| ptree.nil := polytime_fun.eq_nil_aux
| (ptree.node a b) :=
begin
  convert ptree_children (polytime_fun.eq_const_aux a) (polytime_fun.eq_const_aux b),
  ext x, cases x; simp,
end

lemma polytime_fun.eq_const {f : α → β} [decidable_eq β] (hf : polytime_fun f) (x : β) : polytime_fun (λ x', (f x' = x : bool)) :=
begin
  convert_to polytime_fun (λ x', (encode (f x') = encode x : bool)), { simp, },
  exact polytime_fun.comp (polytime_fun.eq_const_aux (encode x)) hf,
end

end bool

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

section option

instance : polycodable (option α) :=
{ encode := λ x, ptree.of_option (x.map encode),
  decode := λ v, (ptree.to_option v).map decode,
  decode_encode := λ x, by simp,
  polytime_decode :=
begin
  rw polytime_fun_iff',
  convert_to polytime_fun (λ x : ptree, if x = ptree.nil then ptree.nil else ptree.of_option (some (encode (decode x.right : α)))),
  { ext x, cases x; simp [ptree.to_option, ptree.of_option], },
  apply polytime_fun.ite, apply polytime_fun.eq_const polytime_fun.id, apply polytime_fun.const,
  simp only [ptree.of_option], apply polytime_fun.comp₂ polytime_fun.node (polytime_fun.const _), apply polytime_fun.comp polytime_fun.encode, apply polytime_fun.comp polytime_fun.decode', apply polytime_fun.ptree_right,
end }

lemma polytime_fun.some : polytime_fun (@some α) :=
by { apply polytime_fun.decode, simp [encode, function.comp, ptree.of_option], apply polytime_fun.comp₂ polytime_fun.node (polytime_fun.const _) polytime_fun.encode, }

lemma polytime_fun.iget [inhabited α] : polytime_fun (@option.iget α _) :=
⟨code.ite code.id (code.const (encode (default : α))) code.right, polytime_ite polytime_id (polytime_const _) polytime_right, λ x,
by { cases x; simp [encode, ptree.of_option], }⟩

lemma polytime_fun.is_none : polytime_fun (@option.is_none α) :=
⟨code.ite code.id (code.const $ encode tt) (code.const $ encode ff), polytime_ite polytime_id (polytime_const _) (polytime_const _), λ x,
by { cases x; simp [encode, ptree.of_option], }⟩

lemma polytime_fun.option_elim {f : α → option β} {g : α → γ} {h : α → β → γ} (hf : polytime_fun f) (hg : polytime_fun g) (hh : polytime_fun₂ h) :
  polytime_fun (λ x, (f x).elim (g x) (h x)) :=
begin
  apply polytime_fun.decode,
  haveI : inhabited β := ⟨decode ptree.nil⟩,
  convert_to polytime_fun (λ x : α, if (f x).is_none then encode (g x) else encode (h x (f x).iget)),
  { ext x, cases H : (f x); simp [H], },
  apply polytime_fun.ite, { simp, apply polytime_fun.comp, apply polytime_fun.is_none, exact hf, },
  apply polytime_fun.comp polytime_fun.encode hg, apply polytime_fun.comp polytime_fun.encode,
  apply polytime_fun.comp₂ hh polytime_fun.id, apply polytime_fun.comp polytime_fun.iget hf,
end

lemma polytime_fun.map {f : α → option β} {g : α → β → γ} (hf : polytime_fun f) (hg : polytime_fun₂ g) :
  polytime_fun (λ x, (f x).map (g x)) :=
begin
  convert_to polytime_fun (λ x, (f x).elim none (λ r, some (g x r))),
  { ext x : 1, cases (f x); simp, },
  apply polytime_fun.option_elim hf, apply polytime_fun.const, simp only [polytime_fun₂, function.uncurry], apply polytime_fun.comp polytime_fun.some hg,
end

end option

section mk

@[simps]
def polycodable.mk' {δ : Type*} (encode : δ → α) (decode : α → δ) (encode_decode : ∀ x, decode (encode x) = x)
  (polytime_decode : polytime_fun (encode ∘ decode)) : polycodable δ :=
{ encode := λ x, polycodable.encode (encode x),
  decode := λ y, decode (polycodable.decode y),
  decode_encode := by simp [encode_decode],
  polytime_decode :=
begin
  rw polytime_fun_iff', apply polytime_fun.comp, apply polytime_fun.encode,
  apply polytime_fun.comp polytime_decode, apply polytime_fun.decode',
end }

lemma polycodable.mk_encode {δ : Type*} (encode : δ → α) (decode : α → δ) (encode_decode : ∀ x, decode (encode x) = x)
  (polytime_decode : polytime_fun (encode ∘ decode)) :
  @polytime_fun δ α (polycodable.mk' encode decode encode_decode polytime_decode) _ encode :=
by { apply polytime_fun.decode, apply polytime_fun.encode, }

lemma polycodable.mk_decode' {δ : Type*} (encode : δ → α) (decode : α → δ) (encode_decode : ∀ x, decode (encode x) = x)
  (polytime_decode : polytime_fun (encode ∘ decode)) :
  @polytime_fun α δ _ (polycodable.mk' encode decode encode_decode polytime_decode) decode :=
polytime_decode


lemma polycodable.mk_decode {δ : Type*} (encode : δ → α) (decode : α → δ) (encode_decode : ∀ x, decode (encode x) = x)
  (polytime_decode : polytime_fun (encode ∘ decode)) (f : β → δ) (hf : polytime_fun (encode ∘ f)) :
  @polytime_fun β δ _ (polycodable.mk' encode decode encode_decode polytime_decode) f :=
hf

end mk

section sum

end sum
