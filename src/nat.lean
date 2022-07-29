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

@[simp] lemma equiv_list_bool_one : equiv_list_bool 1 = [] := rfl
@[simp] lemma equiv_list_bool_bit0 (n : pos_num) :
  equiv_list_bool (bit0 n) = ff :: equiv_list_bool n := rfl
@[simp] lemma equiv_list_bool_bit1 (n : pos_num) :
  equiv_list_bool (bit1 n) = tt :: equiv_list_bool n := rfl
@[simp] lemma equiv_list_bool_symm_cons_tt (l : list bool) :
  equiv_list_bool.symm (tt :: l) = bit1 (equiv_list_bool.symm l) := rfl
@[simp] lemma equiv_list_bool_symm_cons_ff (l : list bool) :
  equiv_list_bool.symm (ff :: l) = bit0 (equiv_list_bool.symm l) := rfl

instance : polycodable pos_num :=
polycodable.of_equiv equiv_list_bool



end pos_num