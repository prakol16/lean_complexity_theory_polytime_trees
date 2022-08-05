import data.num.lemmas
import lists

namespace pos_num
#exit
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
@[simp] lemma equiv_list_bool_symm_cons_tt (l : list bool) :
  equiv_list_bool.symm (tt :: l) = bit1 (equiv_list_bool.symm l) := rfl
@[simp] lemma equiv_list_bool_symm_cons_ff (l : list bool) :
  equiv_list_bool.symm (ff :: l) = bit0 (equiv_list_bool.symm l) := rfl

@[simp] lemma succ_inj_iff {x y : pos_num} : x.succ = y.succ ↔ x = y :=
by { split, { intro h, apply_fun (λ (n : pos_num), (n : ℕ)) at h, simpa using h, }, { rintro rfl, refl, } }

end pos_num

section
variables {α β γ : Type*} [polycodable α] [polycodable β] [polycodable γ]

open pos_num
open polycodable (encode decode)

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
  equiv_list_bool n.succ = (equiv_list_bool n).rec' (λ (l : list bool) (ih : list bool), cond l.head (ff :: ih) (tt :: l.tail)) [ff] :=
begin
  induction n with tl ih tl ih,
  { refl, }, { simp [pos_num.succ, ih], }, { simp [pos_num.succ, ih], }
end

@[simp] lemma polysize_fun.encode_tt_sizeof : (encode tt).sizeof = 1 :=
by simp [encode]

@[simp] lemma polysize_fun.encode_ff_sizeof : (encode ff).sizeof = 3 :=
by simp [encode]

lemma polysize_fun.encode_tail_sizeof_le (l : list α) : (encode l.tail).sizeof ≤ (encode l).sizeof :=
by { cases l; simp, }

@[polyfun]
lemma polytime_fun.pos_num_bit0 : polytime_fun pos_num.bit0 :=
by { convert_to polytime_fun (λ n, equiv_list_bool.symm (ff :: equiv_list_bool n)), { ext n, simp, }, polyfun, }

@[polyfun]
lemma polytime_fun.pos_num_bit1 : polytime_fun pos_num.bit1 :=
by { convert_to polytime_fun (λ n, equiv_list_bool.symm (tt :: equiv_list_bool n)), { ext n, simp, }, polyfun, }

@[simp] lemma encode_pos_num_one : (encode one).sizeof = 1 :=
by { simp [polycodable.encode_pos_num], }

@[simp] lemma encode_pos_num_bit0 (n : pos_num) :
  (encode n.bit0).sizeof = 4 + (encode n).sizeof :=
by { simp [polycodable.encode_pos_num], }

@[simp] lemma encode_pos_num_bit1 (n : pos_num) :
  (encode n.bit1).sizeof = 2 + (encode n).sizeof :=
by { simp [polycodable.encode_pos_num], }

@[polyfun]
lemma polytime_fun.pos_num_succ : polytime_fun pos_num.succ :=
begin
  convert_to polytime_fun (λ n, ((equiv_list_bool n).rec'
    (λ l (ih : pos_num), cond l.head ih.bit0 (equiv_list_bool.symm l.tail).bit1) 2)),
  { ext n, induction n with _ ih _ ih, { refl, }, all_goals { simp [pos_num.succ, ih], }, },
  polyfun,
  use polynomial.monomial 1 1 + 3,
  intros, cases l.head; simp [polycodable.encode_pos_num]; linarith only [polysize_fun.encode_tail_sizeof_le l],
end

lemma pos_num_add_eq : ∀ (m n : pos_num),
  (m.add n) = ((equiv_list_bool m).zip (equiv_list_bool n))
    .foldr (λ bs ih, cond bs.1 
      (cond bs.2 ih.succ.bit0 ih.bit1)
      (cond bs.2 ih.bit1 ih.bit0))
      (if (equiv_list_bool m).length ≤ (equiv_list_bool n).length then 
        (equiv_list_bool.symm ((equiv_list_bool n).drop (equiv_list_bool m).length)).succ
       else 
        (equiv_list_bool.symm ((equiv_list_bool m).drop (equiv_list_bool n).length)).succ)
| 1 m := by { simp, cases m; simp [pos_num.add], refl, }
| n 1 := by { simp, cases n; simp [pos_num.add], refl, }
| (pos_num.bit0 a) (pos_num.bit0 b) := by { simp [pos_num.add], apply pos_num_add_eq, }
| (pos_num.bit1 a) (pos_num.bit1 b) := by { simp [pos_num.add], apply pos_num_add_eq, }
| (pos_num.bit1 a) (pos_num.bit0 b) := by { simp [pos_num.add], apply pos_num_add_eq, }
| (pos_num.bit0 a) (pos_num.bit1 b) := by { simp [pos_num.add], apply pos_num_add_eq, }

lemma polytime_fun.pos_num_add : polytime_fun₂ @pos_num.add :=
begin
  change polytime_fun₂ (λ _ _, _), simp_rw pos_num_add_eq, polyfun,
end


end