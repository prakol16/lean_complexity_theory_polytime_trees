import data.num.lemmas
import lists
import data.nat.digits

namespace nat

lemma size_eq_log_bits_len {n : ℕ} (hn : n ≠ 0) : n.size = log 2 n + 1 :=
by rw [← size_eq_bits_len, ← digits_len _ _ rfl.le (pos_iff_ne_zero.mpr hn), digits_two_eq_bits, list.length_map]

lemma add_size_le (m n : ℕ) : (m + n).size ≤ (max m.size n.size) + 1 :=
by { rw [nat.size_le, pow_succ, two_mul], apply add_lt_add; simp [← size_le], }

end nat

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

@[reducible] def bit_encode_size : ℕ := 5
@[reducible] def bit0_encode : ptree := ptree.node ptree.non_nil ptree.nil
@[reducible] def bit1_encode : ptree := ptree.node ptree.nil ptree.non_nil

lemma bit0_ne_bit1 : bit0_encode ≠ bit1_encode := dec_trivial
@[simp] lemma bit0_encode_sizeof : bit0_encode.sizeof = bit_encode_size := by simp
@[simp] lemma bit1_encode_sizeof : bit1_encode.sizeof = bit_encode_size := by simp

attribute [irreducible] bit_encode_size bit0_encode bit1_encode

@[simp] lemma cond_eq {α} (c : bool) (a b : α) (h : a ≠ b) : cond c a b = a ↔ c :=
by cases c; simp [h.symm]

instance : polycodable pos_num :=
polycodable.mk'
(λ n : pos_num, n.equiv_list_bool.map (λ b, cond b bit1_encode bit0_encode))
(λ l : list ptree, equiv_list_bool.symm (l.map (λ x, (x = bit1_encode : bool)))) 
(λ n, by simp [function.comp, bit0_ne_bit1.symm]) 
(by { simp [function.comp], polyfun, })

lemma polycodable.pos_num_encode (n : pos_num) :
  encode n = encode (n.equiv_list_bool.map (λ b, cond b bit1_encode bit0_encode)) := rfl

lemma polytime_fun.pos_num_encode : polytime_fun (λ n : pos_num, n.equiv_list_bool.map (λ b, cond b bit1_encode bit0_encode)) :=
polytime_fun.id

lemma polytime_fun.pos_num_decode : polytime_fun (λ l : list ptree, equiv_list_bool.symm (l.map (λ l, (l = bit1_encode : bool)))) := 
polycodable.mk_decode' _ _ _ _

@[polyfun]
lemma polytime_fun.pos_num_equiv_list_bool : polytime_fun equiv_list_bool :=
begin
  have := (_ : polytime_fun (λ l : list ptree, l.map (λ x, (x = bit1_encode : bool)))).comp polytime_fun.pos_num_encode,
  simpa [function.comp, bit0_ne_bit1.symm], polyfun,
end

@[polyfun]
lemma polytime_fun.pos_num_equiv_list_bool_symm : polytime_fun equiv_list_bool.symm :=
begin
  have := polytime_fun.pos_num_decode.comp (_ : polytime_fun (λ l : list bool, l.map (λ b, cond b bit1_encode bit0_encode))),
  simpa [function.comp, bit0_ne_bit1.symm], polyfun,
end

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
by simp [polycodable.pos_num_encode]

@[simp] lemma encode_pos_num_bit0 (n : pos_num) : (encode n.bit0).sizeof = (encode n).sizeof + bit_encode_size + 1 :=
by { simp [polycodable.pos_num_encode], ac_refl, }

@[simp] lemma encode_pos_num_bit1 (n : pos_num) : (encode n.bit1).sizeof = (encode n).sizeof + bit_encode_size + 1 :=
by { simp [polycodable.pos_num_encode], ac_refl, }

attribute [simp] pos_num.nat_size

lemma encode_pos_num_sizeof_eq_size (n : pos_num) : ((encode n).sizeof : ℤ) =  n.nat_size * (bit_encode_size + 1) - bit_encode_size :=
by { induction n; simp [*]; ring, }

lemma succ_size_le (n : pos_num) : n.succ.nat_size ≤ n.nat_size + 1 :=
by { induction n, { simp [pos_num.succ], }, { simpa [pos_num.succ, nat.succ_eq_add_one], }, { simp [pos_num.succ], } }

lemma le_of_size_le {n : pos_num} {N : ℕ} (h : n.nat_size ≤ N) :
  ((encode n).sizeof : ℤ) ≤ N * (bit_encode_size + 1) - bit_encode_size :=
by { rw encode_pos_num_sizeof_eq_size, simpa, }

lemma polysize_fun_safe_pos_num_succ (α : Type*) [ptree.pencodable α] : polysize_fun_safe (λ (_ : α) (n : pos_num), n.succ) :=
⟨bit_encode_size + 1,
λ x y, by { zify, refine (le_of_size_le (succ_size_le _)).trans (le_of_eq _), simp [encode_pos_num_sizeof_eq_size], ring, }⟩

lemma add_size_le (m n : pos_num) : (m + n).nat_size ≤ max m.nat_size n.nat_size + 1 :=
by simpa [pos_num.nat_size_to_nat] using nat.add_size_le m n

lemma add_size_le' (m n : pos_num) : (m + n).nat_size ≤ m.nat_size + n.nat_size + 1 :=
by { refine (add_size_le _ _).trans _, simp, }

lemma polysize_fun_safe_pos_num_add : polysize_fun_safe pos_num.add :=
⟨polynomial.monomial 1 1 + 2*bit_encode_size + 1, 
λ m n, by { zify, refine (le_of_size_le (add_size_le' _ _)).trans (le_of_eq _), simp [encode_pos_num_sizeof_eq_size], ring_nf, }⟩

lemma polysize_fun_bit0 (α : Type*) [ptree.pencodable α] : polysize_fun_safe (λ (_ : α), pos_num.bit0) :=
⟨bit_encode_size + 1, λ x y, by { simp [encode_pos_num_sizeof_eq_size], ring_nf, }⟩

lemma polysize_fun_bit1 (α : Type*) [ptree.pencodable α] : polysize_fun_safe (λ (_ : α), pos_num.bit1) :=
⟨bit_encode_size + 1, λ x y, by { simp [encode_pos_num_sizeof_eq_size], ring_nf, }⟩

@[polyfun]
lemma polytime_fun.pos_num_succ : polytime_fun pos_num.succ :=
begin
  convert_to polytime_fun (λ n : pos_num, equiv_list_bool.symm n.succ.equiv_list_bool), { simp, },
  simp_rw pos_num.succ_list_bool, polyfun,
  apply polysize_fun_safe.ite, { simp, apply polysize_of_polytime_fun, polyfun, }, exact polysize_fun_safe.cons.comp (polysize_uniform_of_fin_range _) polysize_fun_safe.id,
end

@[reducible]
private def add'_foldr (bs : bool × bool) (ih : pos_num) : pos_num :=
cond bs.1 (cond bs.2 ih.succ.bit0 ih.bit1) (cond bs.2 ih.bit1 ih.bit0)

private lemma add'_foldr_polytime : polytime_fun₂ add'_foldr :=
by polyfun

local attribute [polyfun] add'_foldr_polytime
private lemma add'_foldr_polysize : polysize_fun_safe add'_foldr :=
begin
  repeat { apply polysize_fun_safe.cond, },
  { apply polysize_fun_safe.comp' (polysize_fun_bit0 _) (polysize_fun_safe_pos_num_succ _), },
  any_goals { apply polysize_fun_bit1, }, apply polysize_fun_bit0,
end

@[reducible]
private def add'_init (m n : pos_num) :=
(if (equiv_list_bool m).length ≤ (equiv_list_bool n).length then 
  (equiv_list_bool.symm ((equiv_list_bool n).drop (equiv_list_bool m).length)).succ
else 
  (equiv_list_bool.symm ((equiv_list_bool m).drop (equiv_list_bool n).length)).succ)

private lemma add'_init_polytime : polytime_fun₂ add'_init := by polyfun
local attribute [polyfun] add'_init_polytime

private def add' (m n : pos_num) : pos_num :=
((equiv_list_bool m).zip (equiv_list_bool n))
  .foldr add'_foldr (add'_init m n)

@[simp] private lemma add'_case0 (m : pos_num) : add' 1 m = m.succ := by simp [add', add'_init]
@[simp] private lemma add'_case1 (n : pos_num) : add' n 1 = n.succ := by simpa [add', add'_init] using eq.symm
@[simp] private lemma add'_case2 (m n : pos_num) : add' m.bit0 n.bit0 = (add' m n).bit0 := by simp [add', add'_foldr, add'_init]
@[simp] private lemma add'_case3 (m n : pos_num) : add' m.bit1 n.bit1 = (add' m n).succ.bit0 := by simp [add', add'_init, add'_foldr]
@[simp] private lemma add'_case4 (m n : pos_num) : add' m.bit0 n.bit1 = (add' m n).bit1 := by simp [add', add'_init, add'_foldr]
@[simp] private lemma add'_case5 (m n : pos_num) : add' m.bit1 n.bit0 = (add' m n).bit1 := by simp [add', add'_init, add'_foldr]

lemma add_eq_add (m n : pos_num) : m.add n = m + n := rfl

lemma pos_num_add_eq : ∀ (m n : pos_num),
  (m.add n) = add' m n
| 1 m := by simp [one_add, add_eq_add]
| n 1 := by simp [add_one, add_eq_add]
| (pos_num.bit0 a) (pos_num.bit0 b) := by simpa [pos_num.add] using pos_num_add_eq a b
| (pos_num.bit1 a) (pos_num.bit1 b) := by simpa [pos_num.add] using pos_num_add_eq a b
| (pos_num.bit1 a) (pos_num.bit0 b) := by simpa [pos_num.add] using pos_num_add_eq a b
| (pos_num.bit0 a) (pos_num.bit1 b) := by simpa [pos_num.add] using pos_num_add_eq a b

local attribute [semireducible] add'_foldr
local attribute [semireducible] add'_init

private lemma polytime_fun.pos_num_add' : polytime_fun₂ add' :=
begin
  change polytime_fun₂ (λ _ _, _), polyfun, apply add'_foldr_polysize.comp,
  { simp, apply polysize_of_polytime_fun, polyfun, }, { apply polysize_fun_safe.id, }
end

@[polyfun]
lemma polytime_fun.pos_num_add : polytime_fun₂ pos_num.add :=
by { change polytime_fun₂ (λ _ _, _), simp_rw pos_num_add_eq, exact polytime_fun.pos_num_add', }

@[polyfun]
lemma polytime_fun.pos_num_add' : polytime_fun₂ ((+) : pos_num → pos_num → pos_num) :=
polytime_fun.pos_num_add

lemma polytime_fun.pos_num_mul : polytime_fun₂ pos_num.mul :=
begin
  convert_to polytime_fun₂ (λ (a b : pos_num), (equiv_list_bool b).foldr (λ (b : bool) (acc : pos_num), cond b (a + acc.bit0) acc.bit0) a),
  { ext a b, induction b; simp [pos_num.mul, *, add_comm], },
  polyfun, apply polysize_fun_safe.cond, { apply polysize_fun_safe_pos_num_add.comp, { simp, apply polysize_of_polytime_fun, polyfun, }, { exact polysize_fun_bit0 _, } },
  exact polysize_fun_bit0 _,
end

end