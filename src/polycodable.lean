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

@[irreducible]
lemma mem_poly (α : Type*) [polycodable α] : polydecidable (∈ set.range (@encode α _)) := polycodable.mem_poly'

def polytime_fun {α β : Type*} [polycodable α] [polycodable β] (f : α → β) :=
∃ (c : code) (pc : polytime c), ∀ x, c.eval (encode x) = part.some (encode (f x))

lemma polydecidable.of_eq {P₁ : α → Prop} (P₂ : α → Prop) (h : ∀ x, P₁ x ↔ P₂ x) : polydecidable P₁ ↔ polydecidable P₂ :=
by rw [(show P₁ = P₂, by { ext, rw h, })]

section polytime_fun

lemma polytime_fun.encode : polytime_fun (@encode α _) :=
⟨code.id, polytime_id, λ x, by simp⟩

lemma polytime_fun.decode {f : α → β} (hf : polytime_fun (encode ∘ f)) : polytime_fun f := hf

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

lemma polytime_fun.polytime_to_fun {c : code} (pc : polytime c) :
  polytime_fun pc.to_fun :=
⟨c, pc, λ x, by simp [polytime.to_fun]⟩

lemma polydecidable.true : @polydecidable α _ (λ _, true) :=
⟨code.nil, polytime_nil, λ x, by simp⟩

lemma polydecidable.or {P₁ P₂ : α → Prop} : polydecidable P₁ → polydecidable P₂ → polydecidable (λ x, (P₁ x) ∨ (P₂ x)) :=
begin
  classical,
  rintros h₁ ⟨c₂, pc₂, s₂⟩,
  suffices : polytime_fun (λ x, if P₁ x then ptree.nil else pc₂.to_fun (encode x)),
  { rcases this with ⟨c, pc, s⟩, use [c, pc], intro x,
    by_cases h : P₁ x, { simp [s, h], },
    simp [s, h, pfun.to_fun, s₂], },
  apply polytime_fun.ite h₁ (polytime_fun.const _) _, apply polytime_fun.comp, apply polytime_fun.polytime_to_fun, apply polytime_fun.encode,
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
  rw polydecidable.of_eq (λ x, x ≠ ptree.nil ∧ x.left = a ∧ x.right = b), swap,
  { intro x, cases x; simp, },
  exact polydecidable.children (eq_const_aux a) (eq_const_aux b),
end

lemma polydecidable.eq_const (x : α) : polydecidable (=x) :=
let ⟨c, pc, s⟩ := eq_const_aux (encode x) in ⟨c, pc, λ x', by simpa using s (encode x')⟩

section pair

instance : polycodable (α × β) :=
{ encode := ⟨λ x, ptree.node (encode x.1) (encode x.2), λ ⟨a₁, b₁⟩ ⟨a₂, b₂⟩, by simpa using and.intro⟩,
  mem_poly' :=
begin
  rw polydecidable_aux_iff,
  rw polydecidable.of_eq (λ x, x ≠ ptree.nil ∧ x.left ∈ set.range (@encode α _) ∧ x.right ∈ set.range (@encode β _)),
  swap, { intro x, split,
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

@[simp] lemma encode_pair_encode_fst (x : α) (y : β) : encode (encode x, y) = encode (x, y) := rfl
@[simp] lemma encode_pair_encode_snd (x : α) (y : β) : encode (x, encode y) = encode (x, y) := rfl

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
    apply polydecidable_of_preimage_polytime (=tt) h, apply polydecidable.eq_const _, }
end

end bool

def polycodable.mk' {δ : Type*} (encode : δ ↪ α) (mem_poly : polydecidable (∈ set.range encode)) : polycodable δ :=
{ encode := encode.trans polycodable.encode,
  mem_poly' :=
begin
  rw polydecidable_aux_iff,
  rcases mem_poly with ⟨c, pc, s⟩,
  rw polydecidable.of_eq (λ x, x ∈ set.range (@polycodable.encode α _) ∧ pc.to_fun x = ptree.nil), swap,
  { intro x, split,
    { intro h, rcases h with ⟨z, hz⟩,
    have : x ∈ set.range (@polycodable.encode α _) := ⟨encode z, by simpa using hz⟩, 
    refine ⟨this, _⟩, rcases this with ⟨x', rfl⟩,
    simp only [polytime.to_fun, part.get_eq_iff_mem, s], use z, simpa using hz, },
    { rintro ⟨⟨y, rfl⟩, H⟩, simpa [part.get_eq_iff_mem, s] using H }, },
  apply polydecidable.and, { exact _root_.mem_poly _, },
  apply polydecidable_of_preimage_polytime (=ptree.nil), { apply polytime_fun.polytime_to_fun, }, apply polydecidable.eq_const,
end }

lemma polytime_fun.encode' {δ : Type*} (encode : δ ↪ α) (mem_poly : polydecidable (∈ set.range encode)) :
  @polytime_fun δ α (polycodable.mk' encode mem_poly) _ encode :=
by { haveI : polycodable δ := polycodable.mk' encode mem_poly, use [code.id, polytime_id], intro x, simp, refl, }

lemma polytime_fun.decode' {δ : Type*} (encode : δ ↪ α) (mem_poly : polydecidable (∈ set.range encode))
  {f : β → δ} (pg : polytime_fun (encode ∘ f)) : @polytime_fun β δ _ (polycodable.mk' encode mem_poly) f := pg

def polycodable.of_equiv {δ : Type*} (eqv : δ ≃ α) : polycodable δ :=
polycodable.mk' eqv.to_embedding
(by simpa [equiv.to_embedding] using polydecidable.true)

lemma polytime_fun.encode_eqv {δ : Type*} (eqv : δ ≃ α) :
  @polytime_fun δ α (polycodable.of_equiv eqv) _ eqv :=
polytime_fun.encode' eqv.to_embedding _

lemma polytime_fun.decode_eqv {δ : Type*} (eqv : δ ≃ α) :
  @polytime_fun α δ _ (polycodable.of_equiv eqv) eqv.symm :=
polytime_fun.decode' eqv.to_embedding _ (by simpa [equiv.to_embedding] using polytime_fun.id)

section unit

@[simp] lemma range_punit {δ : Type*} (f : punit → δ) : set.range f = { f punit.star } :=
begin
  ext x, split,
  { rintro ⟨u, hu⟩, rw (show u = punit.star, by simp) at hu, rw hu, simp, },
  rintro ⟨rfl⟩, exact set.mem_range_self _,
end

instance : polycodable unit :=
{ encode := function.embedding.punit ptree.nil,
  mem_poly' := by { simp [function.embedding.punit], apply polydecidable.eq_const, } }

end unit

section sum

def encode_sum : α ⊕ β → bool × ptree
| (sum.inl a) := (tt, encode a)
| (sum.inr b) := (ff, encode b)

lemma encode_sum_injective : function.injective (@encode_sum α β _ _) :=
λ x y, by cases x; cases y; simp [encode_sum]

lemma mem_encode_sum_decidable : polydecidable (∈ set.range (@encode_sum α β _ _)) :=
begin
  rw polydecidable.of_eq (λ x : bool × ptree, x.1 = tt ∧ x.2 ∈ set.range (@encode α _) ∨ x.1 = ff ∧ x.2 ∈ set.range (@encode β _)),
  swap, { rintro ⟨b, x⟩, cases b; simp [encode_sum], },
  apply polydecidable.or; apply polydecidable.and,
  { apply polydecidable_of_preimage_polytime _ (polytime_fun.prod_fst) (polydecidable.eq_const tt), },
  { apply polydecidable_of_preimage_polytime _ polytime_fun.prod_snd (mem_poly α), },
  { apply polydecidable_of_preimage_polytime _ polytime_fun.prod_fst (polydecidable.eq_const ff), },
  { apply polydecidable_of_preimage_polytime _ polytime_fun.prod_snd (mem_poly β), },
end

instance : polycodable (α ⊕ β) :=
polycodable.mk' ⟨encode_sum, encode_sum_injective⟩ mem_encode_sum_decidable

private lemma polytime_fun_encode_sum : polytime_fun (@encode_sum α β _ _) :=
polytime_fun.encode' _ _

lemma polytime_fun.sum_inl : polytime_fun (@sum.inl α β) :=
begin
  apply polytime_fun.decode',
  change polytime_fun (λ x : α, (tt, encode x)),
  apply polytime_fun.pair, apply polytime_fun.const, apply polytime_fun.encode,
end

lemma polytime_fun.sum_inr : polytime_fun (@sum.inr α β) :=
begin
  apply polytime_fun.decode',
  change polytime_fun (λ x : β, (ff, encode x)),
  apply polytime_fun.pair, apply polytime_fun.const, apply polytime_fun.encode,
end

lemma polytime_fun.sum_elim {δ : Type*} [polycodable δ] 
  {f : α → β ⊕ γ} {g : α → β → δ} {h : α → γ → δ} (hf : polytime_fun f) (hg : polytime_fun₂ g) (hh : polytime_fun₂ h) :
  polytime_fun (λ x, (f x).elim (g x) (h x)) :=
begin
  rcases hg with ⟨gc, pgc, sg⟩, rcases hh with ⟨hc, phc, sh⟩,
  apply polytime_fun.decode,
  convert_to polytime_fun (λ x : α,
  if (encode_sum $ f x).1 = tt then pgc.to_fun (encode $ (x, (encode_sum $ f x).2))
  else phc.to_fun (encode $ (x, (encode_sum $ f x).2))),
  { ext x, simp only [function.comp_app], cases f x, simp [encode_sum, sg (x, val)], simp [encode_sum, sh (x, val)], },
  clear sg sh,
  apply polytime_fun.ite,
  { apply polydecidable_of_preimage_polytime (=tt), apply polytime_fun.comp, apply polytime_fun.prod_fst, apply polytime_fun.comp, apply polytime_fun_encode_sum, exact hf, apply polydecidable.eq_const, },
  apply polytime_fun.comp, apply polytime_fun.polytime_to_fun, apply polytime_fun.comp, apply polytime_fun.encode,
  apply polytime_fun.pair, apply polytime_fun.id, apply polytime_fun.comp, apply polytime_fun.prod_snd, apply polytime_fun.comp, apply polytime_fun_encode_sum, exact hf,
  apply polytime_fun.comp, apply polytime_fun.polytime_to_fun, apply polytime_fun.pair, apply polytime_fun.id, apply polytime_fun.comp, apply polytime_fun.prod_snd, apply polytime_fun.comp, apply polytime_fun_encode_sum, exact hf,
end

lemma polytime_fun.sum_map {δ ε : Type*} [polycodable δ] [polycodable ε]
  {f : α → β ⊕ γ} {g : α → β → δ} {h : α → γ → ε} (hf : polytime_fun f) (hg : polytime_fun₂ g) (hh : polytime_fun₂ h) :
  polytime_fun (λ x : α, (f x).map (g x) (h x)) :=
begin
  convert_to polytime_fun (λ x : α, (f x).elim (λ a : β, sum.inl (g x a)) (λ b : γ, sum.inr (h x b))),
  { ext x, cases (f x); simp, },
  apply polytime_fun.sum_elim hf, dsimp only [polytime_fun₂, function.uncurry], apply polytime_fun.comp, apply polytime_fun.sum_inl, exact hg, dsimp only [polytime_fun₂, function.uncurry], apply polytime_fun.comp, apply polytime_fun.sum_inr, exact hh,
end

end sum

section option

instance : polycodable (option α) :=
polycodable.of_equiv (equiv.option_equiv_sum_punit.{0} α)

lemma polytime_fun.option_equiv_sum_unit : polytime_fun (equiv.option_equiv_sum_punit.{0} α) :=
polytime_fun.encode_eqv _

lemma polytime_fun.option_equiv_sum_unit_symm : polytime_fun (equiv.option_equiv_sum_punit.{0} α).symm :=
polytime_fun.decode_eqv _

lemma polytime_fun.some : polytime_fun (@some α) :=
begin
  change polytime_fun (λ x, (equiv.option_equiv_sum_punit.{0} α).symm (sum.inl x)),
  apply polytime_fun.comp polytime_fun.option_equiv_sum_unit_symm polytime_fun.sum_inl,
end

lemma polytime_fun.option_elim {f : α → option β} {g : α → β → γ} {h : α → γ}
  (hf : polytime_fun f) (hg : polytime_fun₂ g) (hh : polytime_fun h) :
  polytime_fun (λ x, (f x).elim (h x) (g x)) :=
begin
  convert_to polytime_fun (λ x, ((equiv.option_equiv_sum_punit.{0} β) (f x)).elim (λ y, g x y) (λ _, h x)),
  { ext x, cases f x; simp, },
  apply polytime_fun.sum_elim, apply polytime_fun.comp polytime_fun.option_equiv_sum_unit hf,
  exact hg,
  apply polytime_fun.comp hh polytime_fun.prod_fst,
end

end option

noncomputable def polytime_fun.norm_code {f : α → β} (hf : polytime_fun f) :=
code.ite (mem_poly α).some (Exists.some hf) code.nil

lemma polytime_fun.polytime_norm_code {f : α → β} (hf : polytime_fun f) :
  polytime hf.norm_code :=
polytime_ite (mem_poly α).some_spec.some hf.some_spec.some polytime_nil

lemma polytime_fun.norm_code_dom {f : α → β} (hf : polytime_fun f) :
  hf.norm_code.eval.dom = set.univ := hf.polytime_norm_code.dom_univ

@[simp] lemma polytime_fun.norm_code_eval {f : α → β} (hf : polytime_fun f) (x : α) :
  hf.norm_code.eval (encode x) = part.some (encode $ f x) :=
begin
  obtain ⟨_, spec⟩ := Exists.some_spec hf,
  obtain ⟨_, spec'⟩ := Exists.some_spec (mem_poly α),
  specialize spec' (encode x),
  simp only [iff_true, set.mem_range_self] at spec',
  rw [ptree_encode, ← part.eq_some_iff] at spec',
  simp only [polytime_fun.norm_code, spec x, ite_eval, code.eval, spec'],
  simp,
end

lemma polytime_fun.norm_code_invalid {f : α → β} (hf : polytime_fun f) {x : ptree} (hx : x ∉ set.range (@encode α _)) :
  hf.norm_code.eval x = part.some ptree.nil :=
begin
  obtain ⟨p, spec⟩ := Exists.some_spec (mem_poly α), specialize spec x,
  have := p.dom_univ' x, rw [part.dom_iff_mem] at this,
  cases this with y hy, rw ← part.eq_some_iff at hy,
  simp only [iff_false, hx] at spec, rw [ptree_encode, hy] at spec,
  simp at spec, rw @comm _ (=) at spec,
  simp only [polytime_fun.norm_code, code.eval, ite_eval, hy],
  simp only [part.bind_eq_bind, spec, part.some_inj, eq_self_iff_true, if_false, part.bind_some],
end

end polytime_fun

