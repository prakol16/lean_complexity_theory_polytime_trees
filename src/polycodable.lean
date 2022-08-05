import polycodable_init
import polytime_tac

variables {α β γ : Type*} [polycodable α] [polycodable β] [polycodable γ]
open ptree.pencodable (encode decode)

section bool

instance : polycodable bool :=
{ polytime_decode := ⟨_, 
  (polytime_ite polytime_id polytime_nil (polytime_const ptree.non_nil)), λ x, by cases x; simp [ptree.of_option, encode, decode]⟩ }

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
{ polytime_decode :=
begin
  convert_to polytime_fun (λ x : ptree, if x = ptree.nil then ptree.nil else ptree.of_option (some (encode (decode x.right : α)))),
  { ext x, cases x; simp [ptree.to_option, ptree.of_option, encode, decode], },
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

@[polyfun]
lemma polytime_fun.get_or_else : polytime_fun₂ (@option.get_or_else α) :=
begin
  convert_to polytime_fun₂ (λ (a : option α) (b : α), a.elim b id),
  { ext a b, cases a; simp, }, polyfun,
end

@[polyfun]
lemma polytime_fun.is_some : polytime_fun (@option.is_some α) :=
begin
  convert_to polytime_fun (λ (a : option α), a.elim ff (λ _, tt)),
  { ext x, cases x; simp, }, polyfun,
end

end option

section mk

def polycodable.mk' {δ : Type*} (encode : δ → α) (decode : α → δ) (encode_decode : ∀ x, decode (encode x) = x)
  (polytime_decode : polytime_fun (encode ∘ decode)) : polycodable δ :=
{ polytime_decode :=
by { apply polytime_fun.comp polytime_decode, polyfun, },
  ..ptree.pencodable.mk' encode decode encode_decode, }

lemma polycodable.mk_encode {δ : Type*} (encode : δ → α) (decode : α → δ) (encode_decode : ∀ x, decode (encode x) = x) :
  @polytime_fun δ α (ptree.pencodable.mk' encode decode encode_decode) _ encode :=
by { apply polytime_fun.id, }

lemma polycodable.mk_decode' {δ : Type*} (encode : δ → α) (decode : α → δ) (encode_decode : ∀ x, decode (encode x) = x)
  (polytime_decode : polytime_fun (encode ∘ decode)) :
  @polytime_fun α δ _ (polycodable.mk' encode decode encode_decode polytime_decode).to_pencodable decode :=
polytime_decode

lemma polycodable.mk_decode {δ : Type*} (encode : δ → α) (decode : α → δ) (encode_decode : ∀ x, decode (encode x) = x)
  (f : β → δ) (hf : polytime_fun (encode ∘ f)) :
  @polytime_fun β δ _ (ptree.pencodable.mk' encode decode encode_decode) f :=
hf

def polycodable.of_equiv {δ : Type*} (eqv : δ ≃ α) : polycodable δ :=
polycodable.mk'
(λ x, eqv x)
(λ y, eqv.symm y)
(by simp)
(by simpa using polytime_fun.id)

@[polyfun]
lemma polycodable.of_equiv_polytime {δ : Type*} (eqv : δ ≃ α) :
  @polytime_fun δ α (ptree.pencodable.of_equiv eqv) _ eqv :=
by { apply polytime_fun.id, }

@[polyfun]
lemma polycodable.of_equiv_polytime_symm {δ : Type*} (eqv : δ ≃ α) :
  @polytime_fun α δ _ (polycodable.of_equiv eqv).to_pencodable eqv.symm :=
by { apply polycodable.mk_decode', }

end mk

section unit

instance : polycodable unit := 
{ polytime_decode := polytime_fun.const ptree.nil }

end unit

section sum

end sum
