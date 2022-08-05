import data.num.lemmas
import lists

namespace pos_num
def to_trailing_bits : pos_num → list bool
| 1 := []
| (bit0 xs) := ff :: xs.to_trailing_bits
| (bit1 xs) := tt :: xs.to_trailing_bits

/-- Equivalence between `pos_num` and `list bool` with lsb at the head and msb omitted -/
def equiv_list_bool : pos_num ≃ list bool :=
{ to_fun := to_trailing_bits,
  inv_fun := λ l, l.foldr (λ b n, (cond b bit1 bit0) n) 1,
  left_inv := λ n, by induction n; simpa [to_trailing_bits],
  right_inv := λ l, by { induction l with hd, { refl, }, cases hd; simpa [to_trailing_bits], } }

@[simp] lemma one_eq_one : one = 1 := rfl
@[simp] lemma equiv_list_bool_one : equiv_list_bool 1 = [] := rfl
@[simp] lemma equiv_list_bool_bit0 (n : pos_num) :
  equiv_list_bool (bit0 n) = ff :: equiv_list_bool n := rfl
@[simp] lemma equiv_list_bool_bit1 (n : pos_num) :
  equiv_list_bool (bit1 n) = tt :: equiv_list_bool n := rfl
@[simp] lemma equiv_list_bool_symm_nil : equiv_list_bool.symm [] = 1 := rfl
@[simp] lemma equiv_list_bool_symm_cons_tt (l : list bool) :
  equiv_list_bool.symm (tt :: l) = bit1 (equiv_list_bool.symm l) := rfl
@[simp] lemma equiv_list_bool_symm_cons_ff (l : list bool) :
  equiv_list_bool.symm (ff :: l) = bit0 (equiv_list_bool.symm l) := rfl
@[simp] lemma equiv_list_bool_len_zero_iff (n : pos_num) : (equiv_list_bool n).length = 0 ↔ n = 1 :=
by simp [list.length_eq_zero, equiv.apply_eq_iff_eq_symm_apply]


@[simp] lemma succ_inj_iff {x y : pos_num} : x.succ = y.succ ↔ x = y :=
by { split, { intro h, apply_fun (λ (n : pos_num), (n : ℕ)) at h, simpa using h, }, { rintro rfl, refl, } }

end pos_num

section
variables {α β γ : Type*} [polycodable α] [polycodable β] [polycodable γ]

open pos_num
open ptree.pencodable (encode decode)

local attribute [instance] unary_nat_encode

instance : polycodable pos_num :=
polycodable.of_equiv equiv_list_bool

lemma polycodable.encode_pos_num (n : pos_num) : encode n = encode (equiv_list_bool n) := rfl

@[polyfun]
lemma polytime_fun.pos_num_equiv_list_bool : polytime_fun equiv_list_bool :=
by polyfun

@[polyfun]
lemma polytime_fun.pos_num_equiv_list_bool_sym : polytime_fun equiv_list_bool.symm :=
by polyfun

lemma pos_num.succ_list_bool (n : pos_num) :
  equiv_list_bool n.succ = (equiv_list_bool n).tails.foldr (λ (l : list bool) (ih : list bool), if l.head' = some ff then tt :: l.tail else ff :: ih) [] :=
begin
  induction n with tl ih tl ih,
  { refl, }, { simp [pos_num.succ, ih], }, { simp [pos_num.succ, ih], }
end

@[polyfun]
lemma polytime_fun.pos_num_bit0 : polytime_fun pos_num.bit0 :=
by { convert_to polytime_fun (λ n, equiv_list_bool.symm (ff :: equiv_list_bool n)), { ext n, simp, }, polyfun, }

@[polyfun]
lemma polytime_fun.pos_num_bit1 : polytime_fun pos_num.bit1 :=
by { convert_to polytime_fun (λ n, equiv_list_bool.symm (tt :: equiv_list_bool n)), { ext n, simp, }, polyfun, }

@[simp] lemma encode_pos_num_one : (encode (1 : pos_num)).sizeof = 1 :=
by { simp [polycodable.encode_pos_num], }

@[simp] lemma encode_pos_num_bit0 (n : pos_num) :
  (encode n.bit0).sizeof = (encode n).sizeof + 4 :=
by { simp [polycodable.encode_pos_num, add_comm], }

@[simp] lemma encode_pos_num_bit1 (n : pos_num) :
  (encode n.bit1).sizeof = (encode n).sizeof + 2 :=
by { simp [polycodable.encode_pos_num, add_comm], }

lemma polysize_fun_safe.bit0 (α : Type*) [ptree.pencodable α] : polysize_fun_safe (λ (_ : α) (n : pos_num), n.bit0) :=
⟨4, λ _ _, by simp⟩

lemma polysize_fun_safe.bit1 (α : Type*) [ptree.pencodable α] : polysize_fun_safe (λ (_ : α) (n : pos_num), n.bit1) :=
⟨2, λ _ _, by simp⟩

@[polyfun]
lemma polytime_fun.pos_num_succ : polytime_fun pos_num.succ :=
begin
  convert_to polytime_fun (λ n : pos_num, equiv_list_bool.symm n.succ.equiv_list_bool), { simp, },
  simp_rw pos_num.succ_list_bool, polyfun, /- TODO: Fix -/ { apply polytime_fun.comp; polyfun, },
  apply polysize_fun_safe.ite, { simp, apply polysize_of_polytime_fun, polyfun, }, exact polysize_fun_safe.cons.comp (polysize_uniform_of_fin_range _) polysize_fun_safe.id,
end

private def add' (m n : pos_num) : pos_num :=
((equiv_list_bool m).zip (equiv_list_bool n))
  .foldr (λ bs ih, cond bs.1 
  (cond bs.2 ih.succ.bit0 ih.bit1)
  (cond bs.2 ih.bit1 ih.bit0))
  (if (equiv_list_bool m).length ≤ (equiv_list_bool n).length then 
    (equiv_list_bool.symm ((equiv_list_bool n).drop (equiv_list_bool m).length)).succ
    else 
    (equiv_list_bool.symm ((equiv_list_bool m).drop (equiv_list_bool n).length)).succ)

@[simp] private lemma add'_case0 (m : pos_num) : add' 1 m = m.succ := by simp [add']
@[simp] private lemma add'_case1 (n : pos_num) : add' n 1 = n.succ := by simpa [add'] using eq.symm
@[simp] private lemma add'_case2 (m n : pos_num) : add' m.bit0 n.bit0 = (add' m n).bit0 := by simp [add']
@[simp] private lemma add'_case3 (m n : pos_num) : add' m.bit1 n.bit1 = (add' m n).succ.bit0 := by simp [add']
@[simp] private lemma add'_case4 (m n : pos_num) : add' m.bit0 n.bit1 = (add' m n).bit1 := by simp [add']
@[simp] private lemma add'_case5 (m n : pos_num) : add' m.bit1 n.bit0 = (add' m n).bit1 := by simp [add']

lemma add_eq_add (m n : pos_num) : m.add n = m + n := rfl

lemma pos_num_add_eq : ∀ (m n : pos_num),
  (m.add n) = add' m n
| 1 m := by simp [one_add, add_eq_add]
| n 1 := by simp [add_one, add_eq_add]
| (pos_num.bit0 a) (pos_num.bit0 b) := by simpa [pos_num.add] using pos_num_add_eq a b
| (pos_num.bit1 a) (pos_num.bit1 b) := by simpa [pos_num.add] using pos_num_add_eq a b
| (pos_num.bit1 a) (pos_num.bit0 b) := by simpa [pos_num.add] using pos_num_add_eq a b
| (pos_num.bit0 a) (pos_num.bit1 b) := by simpa [pos_num.add] using pos_num_add_eq a b

private lemma polytime_fun.pos_num_add' : polytime_fun₂ add' :=
begin
  change polytime_fun₂ (λ _ _, _), polyfun,
end


lemma polytime_fun.pos_num_add : polytime_fun₂ pos_num.add :=
begin
  change polytime_fun₂ (λ _ _, _), simp_rw pos_num_add_eq, --polyfun,
end


end