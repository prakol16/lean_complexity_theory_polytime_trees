import polycodable_init
import polytime_tac

variables {α β γ : Type*} [polycodable α] [polycodable β] [polycodable γ]
open polycodable (encode decode)

section bool

instance : polycodable bool :=
{ encode := λ b, cond b ptree.nil ptree.non_nil,
  decode := λ v, if v = ptree.nil then tt else ff,
  decode_encode := λ b, by cases b; simp,
  polytime_decode := ⟨_, 
  (polytime_ite polytime_id polytime_nil (polytime_const ptree.non_nil)), λ x, by cases x; simp [ptree.of_option]⟩ }

@[polyfun]
lemma polytime_fun.ite' {f : α → bool} {g h : α → β} : polytime_fun f → polytime_fun g → polytime_fun h → polytime_fun (λ x, cond (f x) (g x) (h x))
| ⟨cf, pf, sf⟩ ⟨cg, pg, sg⟩ ⟨ch, ph, sh⟩ :=
⟨_, polytime_ite pf pg ph, λ x, by cases H : (f x); simp [sf, sg, sh, ← apply_ite part.some, ← apply_ite encode, encode, H]⟩ 

@[polyfun]
lemma polytime_fun.ite {P : α → Prop} [decidable_pred P] {g h : α → β} (hP : polytime_fun (λ x, (P x : bool))) (hg : polytime_fun g) (hh : polytime_fun h) :
  polytime_fun (λ x, if P x then g x else h x) :=
begin
  convert_to polytime_fun (λ x, cond (P x) (g x) (h x)),
  { ext x, by_cases P x; simp, }, polyfun,
end


private lemma polytime_fun.eq_nil_aux : polytime_fun (λ x', (x' = ptree.nil : bool)) :=
⟨_, polytime_ite polytime_id polytime_nil (polytime_const ptree.non_nil), λ x, by cases x; simp [encode]⟩

local attribute [polyfun] polytime_fun.eq_nil_aux

@[polyfun]
lemma polytime_fun.band : polytime_fun₂ (&&) :=
begin
  convert_to polytime_fun₂ (λ b₁ b₂ : bool, cond b₁ b₂ ff),
  { ext b₁, cases b₁; simp, }, polyfun,
end

@[polyfun]
lemma polytime_fun.bor : polytime_fun₂ (||) :=
begin
  convert_to polytime_fun₂ (λ b₁ b₂ : bool, cond b₁ tt b₂),
  { ext b₁, cases b₁; simp, }, polyfun,
end

@[polyfun]
lemma polytime_fun.bnot : polytime_fun bnot :=
by { convert_to polytime_fun (λ b, cond b ff tt), { ext b, cases b; refl, }, polyfun, }

lemma ptree_children {f g : ptree → bool} (hf : polytime_fun f) (hg : polytime_fun g) :
  polytime_fun (λ x : ptree, (x ≠ ptree.nil) && (f x.left && g x.right)) :=
by polyfun

private lemma polytime_fun.eq_const_aux : ∀ (x : ptree), polytime_fun (λ x', (x' = x : bool))
| ptree.nil := polytime_fun.eq_nil_aux
| (ptree.node a b) :=
begin
  convert ptree_children (polytime_fun.eq_const_aux a) (polytime_fun.eq_const_aux b),
  ext x, cases x; simp,
end

@[polyfun]
lemma polytime_fun.eq_const {f : α → β} [decidable_eq β] (hf : polytime_fun f) (x : β) : polytime_fun (λ x', (f x' = x : bool)) :=
begin
  convert_to polytime_fun (λ x', (encode (f x') = encode x : bool)), { simp, },
  exact polytime_fun.comp (polytime_fun.eq_const_aux (encode x)) hf,
end

end bool

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
  simp only [ptree.of_option], polyfun,
end }

@[polyfun]
lemma polytime_fun.some : polytime_fun (@some α) :=
by { apply polytime_fun.decode, simp [encode, function.comp, ptree.of_option], polyfun, }

@[polyfun]
lemma polytime_fun.iget [inhabited α] : polytime_fun (@option.iget α _) :=
⟨code.ite code.id (code.const (encode (default : α))) code.right, polytime_ite polytime_id (polytime_const _) polytime_right, λ x,
by { cases x; simp [encode, ptree.of_option], }⟩

@[polyfun]
lemma polytime_fun.is_none : polytime_fun (@option.is_none α) :=
⟨code.ite code.id (code.const $ encode tt) (code.const $ encode ff), polytime_ite polytime_id (polytime_const _) (polytime_const _), λ x,
by { cases x; simp [encode, ptree.of_option], }⟩

@[polyfun]
lemma polytime_fun.option_elim {f : α → option β} {g : α → γ} {h : α → β → γ} (hf : polytime_fun f) (hg : polytime_fun g) (hh : polytime_fun₂ h) :
  polytime_fun (λ x, (f x).elim (g x) (h x)) :=
begin
  apply polytime_fun.decode,
  haveI : inhabited β := ⟨decode ptree.nil⟩,
  convert_to polytime_fun (λ x : α, if (f x).is_none then encode (g x) else encode (h x (f x).iget)),
  { ext x, cases H : (f x); simp [H], },
  polyfun,
end

@[polyfun]
lemma polytime_fun.option_map {f : α → option β} {g : α → β → γ} (hf : polytime_fun f) (hg : polytime_fun₂ g) :
  polytime_fun (λ x, (f x).map (g x)) :=
begin
  convert_to polytime_fun (λ x, (f x).elim none (λ r, some (g x r))),
  { ext x : 1, cases (f x); simp, },
  polyfun,
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
by { rw polytime_fun_iff', polyfun, apply polytime_fun.comp polytime_decode, polyfun, } }

@[polyfun]
lemma polycodable.mk_encode {δ : Type*} (encode : δ → α) (decode : α → δ) (encode_decode : ∀ x, decode (encode x) = x)
  (polytime_decode : polytime_fun (encode ∘ decode)) :
  @polytime_fun δ α (polycodable.mk' encode decode encode_decode polytime_decode) _ encode :=
by { apply polytime_fun.id, }

lemma polycodable.mk_decode' {δ : Type*} (encode : δ → α) (decode : α → δ) (encode_decode : ∀ x, decode (encode x) = x)
  (polytime_decode : polytime_fun (encode ∘ decode)) :
  @polytime_fun α δ _ (polycodable.mk' encode decode encode_decode polytime_decode) decode :=
polytime_decode

@[polyfun]
lemma polycodable.mk_decode {δ : Type*} (encode : δ → α) (decode : α → δ) (encode_decode : ∀ x, decode (encode x) = x)
  (polytime_decode : polytime_fun (encode ∘ decode)) (f : β → δ) (hf : polytime_fun (encode ∘ f)) :
  @polytime_fun β δ _ (polycodable.mk' encode decode encode_decode polytime_decode) f :=
hf

end mk

section sum

end sum
