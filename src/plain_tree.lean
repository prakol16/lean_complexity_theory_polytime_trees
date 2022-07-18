import tactic.simpa
import logic.equiv.basic

@[derive decidable_eq]
inductive ptree
| nil
| node (left : ptree) (right : ptree)

namespace ptree

instance : inhabited ptree := ⟨nil⟩

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
| x := some (ptree.nil.node x)

def of_option : option ptree → ptree
| none := ptree.nil
| (some x) := x.right

@[simp] lemma of_option_to_option (x : ptree) : of_option x.to_option = x :=
by cases x; simp [to_option, of_option]

end ptree