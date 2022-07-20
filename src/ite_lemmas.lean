import tactic.tauto
import tactic.split_ifs

@[simp] lemma sum_inl_eq_ite {α β : Type*} (c : Prop) [decidable c] (x z : α) (y : β) :
  (sum.inl z = if c then sum.inl x else sum.inr y) ↔ c ∧ z = x := by split_ifs; simp; tauto

@[simp] lemma sum_inl_eq_ite_symm {α β : Type*} (c : Prop) [decidable c] (x z : α) (y : β) :
  ((if c then sum.inl x else sum.inr y) = sum.inl z) ↔ c ∧ z = x := by split_ifs; tauto

@[simp] lemma sum_inr_eq_ite {α β : Type*} (c : Prop) [decidable c] (x : α) (y z : β) :
  (sum.inr z = if c then sum.inl x else sum.inr y) ↔ ¬c ∧ z = y := by split_ifs; simp; tauto

@[simp] lemma sum_inr_eq_ite_symm {α β : Type*} (c : Prop) [decidable c] (x : α) (y z : β) :
  ((if c then sum.inl x else sum.inr y) = sum.inr z) ↔ ¬c ∧ z = y := by split_ifs; tauto
