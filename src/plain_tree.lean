import tactic.simpa
import logic.equiv.basic
import logic.encodable.basic
import tactic.apply_fun
import tactic.derive_fintype
import data.tree

@[derive decidable_eq]
inductive ptree
| nil
| node (left : ptree) (right : ptree)

namespace ptree

instance : inhabited ptree := ⟨nil⟩

/-- A non-nil ptree -/
abbreviation non_nil := node nil nil

@[simp] lemma non_nil_ne : non_nil ≠ nil := by trivial

@[simp] def left : ptree → ptree
| nil := nil
| (node l r) := l

@[simp] def right : ptree → ptree
| nil := nil
| (node l r) := r

def elim {α : Type*} (b : α) (f : ptree → ptree → α) : ptree → α
| nil := b
| (node a b) := f a b

attribute [simp] ptree.nil.sizeof_spec
attribute [simp] ptree.node.sizeof_spec

@[simp] lemma sizeof_eq_sizeof (t : ptree) : sizeof t = t.sizeof := rfl

lemma left_sizeof_le (t : ptree) : t.left.sizeof ≤ t.sizeof :=
begin
  cases t, { simp },
  simp only [node.sizeof_spec, left],
  rw [nat.add_comm 1, nat.add_assoc],
  apply nat.le.intro rfl
end

lemma right_sizeof_le (t : ptree) : t.right.sizeof ≤ t.sizeof :=
begin
  cases t, { simp, },
  simp only [node.sizeof_spec, right],
  rw nat.add_comm,
  apply nat.le.intro rfl,
end

@[simp] def reverse : ptree → ptree
| nil := nil
| (node a b) := node b.reverse a.reverse

@[simp] lemma reverse_left (t : ptree) : t.reverse.left = t.right.reverse := by cases t; simp
@[simp] lemma reverse_right (t : ptree) : t.reverse.right = t.left.reverse := by cases t; simp

@[simp] lemma reverse_reverse (t : ptree) : t.reverse.reverse = t := by induction t; simp [*]

def as_list : ptree → list ptree
| nil := []
| (node a b) := a :: b.as_list

def of_list : list ptree → ptree
| [] := nil
| (a :: xs) := node a (of_list xs)

def equiv_list : ptree ≃ list ptree :=
{ to_fun := as_list,
  inv_fun := of_list,
  left_inv := λ t, by { induction t, { simp [as_list, of_list], }, simpa [as_list, of_list] },
  right_inv := λ l, by { induction l, { simp [as_list, of_list], }, simpa [as_list, of_list], } }

@[simp] lemma equiv_list_nil : equiv_list nil = [] := rfl
@[simp] lemma equiv_list_node (a b : ptree) : equiv_list (node a b) = a :: b.equiv_list := rfl
@[simp] lemma equiv_list_symm_nil : equiv_list.symm [] = nil := rfl
@[simp] lemma equiv_list_symm_conds (a : ptree) (b : list ptree) : equiv_list.symm (a :: b) = node a (equiv_list.symm b) := rfl

def to_option : ptree → option ptree
| ptree.nil := none
| x := some x.right

def of_option : option ptree → ptree
| none := ptree.nil
| (some x) := ptree.nil.node x

@[simp] lemma of_option_to_option (x : option ptree) : (of_option x).to_option  = x :=
by cases x; simp [to_option, of_option]

@[simp] lemma to_option_none (x : ptree) : x.to_option = none ↔ x = ptree.nil :=
by cases x; simp [to_option]

@[simp] lemma to_option_some (x v : ptree) : x.to_option = some v ↔ x ≠ ptree.nil ∧ x.right = v :=
by cases x; simp [to_option]

def to_nat : ptree → ℕ
| nil := 0
| (node a b) := (nat.mkpair a.to_nat b.to_nat) + 1

def of_nat : ℕ → ptree
| 0 := nil
| (n + 1) := 
  have wf₁ : (nat.unpair n).1 < n + 1 := nat.lt_succ_of_le (nat.unpair_left_le _),
  have wf₂ : (nat.unpair n).2 < n + 1 := nat.lt_succ_of_le (nat.unpair_right_le _),
node (of_nat (nat.unpair n).1) (of_nat (nat.unpair n).2)

@[simp] lemma of_nat_to_nat (x : ptree) : of_nat x.to_nat = x :=
by { induction x; simp [of_nat, to_nat, *], }

instance : encodable ptree :=
{ encode := ptree.to_nat,
  decode := some ∘ ptree.of_nat,
  encodek := λ x, by simp }

class pencodable (α : Type*) :=
(encode : α → ptree)
(decode : ptree → α)
(encodek : ∀ x, decode (encode x) = x)

attribute [simp, higher_order] pencodable.encodek
namespace pencodable

variables {α β : Type*} [pencodable α] [pencodable β]

instance encode_ptree : pencodable ptree := ⟨id, id, λ _, rfl⟩
@[simp] lemma encode_ptree_def : (@encode ptree _) = id := rfl
@[simp] lemma decode_ptree_def : (@decode ptree _) = id := rfl

instance : pencodable (α × β) :=
{ encode := λ x, node (encode x.1) (encode x.2),
  decode := λ y, (decode y.left, decode y.right),
  encodek := λ x, by simp }
lemma encode_pair_def (x : α) (y : β) : encode (x, y) = node (encode x) (encode y) := rfl
lemma decode_pair_def (v : ptree) : @decode (α × β) _ v = (decode v.left, decode v.right) := rfl

@[priority 50]
instance : nonempty α := ⟨decode nil⟩

instance : pencodable bool :=
{ encode := λ b, cond b ptree.nil ptree.non_nil,
  decode := λ v, v = ptree.nil,
  encodek := λ b, by cases b; simp }
lemma encode_bool_def (b : bool) : encode b = cond b ptree.nil ptree.non_nil := rfl
lemma decode_bool_def (v : ptree) : (decode v : bool) ↔ v = ptree.nil := by simp [decode]
lemma decode_bool_def' (v : ptree) : (decode v : bool) = (v = ptree.nil) := rfl

instance : pencodable unit :=
{ encode := λ _, ptree.nil,
  decode := λ _, (),
  encodek := λ x, by simp }
lemma encode_unit_def : encode () = nil := rfl

protected def mk' {γ : Type*} (enc : γ → α) (dec : α → γ) (h : ∀ x, dec (enc x) = x): pencodable γ :=
{ encode := λ x, encode (enc x),
  decode := λ y, dec (decode y),
  encodek := λ x, by simp [h] }

def of_equiv {γ : Type*} (eqv : γ ≃ α) : pencodable γ :=
pencodable.mk' eqv eqv.symm (by simp)

instance : pencodable (list α) :=
{ encode := λ l, equiv_list.symm (l.map encode),
  decode := λ v, v.equiv_list.map decode,
  encodek := λ l, by simp }
lemma encode_list_def (l : list α) : encode l = equiv_list.symm (l.map encode) := rfl

lemma decode_list_def (v : ptree) : (decode v : list α) = v.equiv_list.map decode := rfl

@[simp] lemma encode_ptree_list (l : list ptree) :
  encode l = equiv_list.symm l :=
by simp [encode_list_def]

@[simp] lemma decode_ptree_list (l : ptree) :
  (decode l : list ptree) = l.equiv_list :=
by simp [decode_list_def]

lemma encode_injective : function.injective (@encode α _) :=
function.left_inverse.injective encodek

@[simp] lemma encode_inj_iff {x y : α} : encode x = encode y ↔ x = y :=
(@encode_injective α _).eq_iff

instance : pencodable (option α) :=
{ encode := λ x, ptree.of_option (x.map encode),
  decode := λ v, (ptree.to_option v).map decode,
  encodek := λ x, by simp, }

def to_encodable : encodable α :=
encodable.of_left_inverse encode decode (by simp)

end pencodable

universes u

@[simp]
def crec {α : Type u} {motive : Type u} (base : α → motive) (pre₁ pre₂ : ptree → α → α) (post : motive → motive → ptree → α → motive) : ptree → α → motive
| nil d := base d
| T@(node x y) d := post (crec x (pre₁ T d)) (crec y (pre₂ T d)) T d

lemma _root_.list.map_head' {α β} (x : list α) (f : α → β) :
  (x.map f).head' = x.head'.map f :=
by cases x; simp

inductive iterator_stack (α β : Type*)
| start : ptree → α → iterator_stack
| mid : ptree → α → β → iterator_stack
| result : β → iterator_stack

-- Rules:
-- If res ≠ none:
    -- If prev.left_res ≠ none:
      -- prev.left_res = res
    -- Else:
      -- prev.res = post prev.left_res res prev.tree prev.arg
    -- delete current
-- Else If tree ≠ nil:
    -- if left_res = none:
      -- append tree.left to stack with arg = pre₁ tree arg
    -- else:
      -- append tree.right to stack with arg = pre₂ tree arg
-- Else (i.e. res = none ∧ tree = nil):
    -- res := base arg

variables {α : Type u} {β : Type u} (base : α → β) (pre₁ pre₂ : ptree → α → α) (post : β → β → ptree → α → β)
open iterator_stack
@[simp] def stack_step :
  list (iterator_stack α β) → list (iterator_stack α β) 
| (result res :: start tree arg :: xs) := mid tree arg res :: xs
| (result res :: mid tree arg left_res :: xs) := result (post left_res res tree arg) :: xs
| L@(mid tree arg left_res :: xs) := (start tree.right (pre₂ tree arg)) :: L
| (start nil arg :: xs) := result (base arg) :: xs
| L@(start (node x y) arg :: xs) := start x (pre₁ (node x y) arg) :: L
| x := x

@[simp] lemma stack_step_nil : stack_step base pre₁ pre₂ post [] = [] := rfl
@[simp] lemma stack_step_singleton (res : β) : stack_step base pre₁ pre₂ post [result res] = [result res] := rfl

def time_steps : ptree → ℕ
| nil := 1
| (node a b) := a.time_steps + b.time_steps + 4

@[simp] lemma time_steps_nil : time_steps nil = 1 := rfl
lemma time_steps_node (a b) : time_steps (node a b) = 1 + b.time_steps + 2 + a.time_steps + 1 :=
by { rw [time_steps, (show 4 = 1 + 2 + 1, from rfl)], ac_refl, } 

lemma stack_step_iterate (x : ptree) (arg : α) (xs : list (iterator_stack α β)) :
  (stack_step base pre₁ pre₂ post)^[x.time_steps] (start x arg :: xs) = (result $ x.crec base pre₁ pre₂ post arg) :: xs :=
by induction x generalizing arg xs; simp [time_steps_node, function.iterate_add, *]

-- example : stack_step base pre₁ pre₂ post = id :=
-- by { ext x : 1, delta stack_step, delta id_rhs, dsimp, }

@[simp] def length : ptree → ℕ
| nil := 1
| (node a b) := a.length + b.length

end ptree
