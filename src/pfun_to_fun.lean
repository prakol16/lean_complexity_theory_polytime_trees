import time_bound

namespace pfun

variables {α β : Type*} (f : α →. β)

def to_fun (hf : f.dom = set.univ) : α → β := λ x, (f x).get (by { change x ∈ f.dom, rw hf, trivial, })

@[simp] lemma coe_to_fun (hf : f.dom = set.univ) : (f.to_fun hf : α →. β) = f :=
by { ext, simp [to_fun], }

end pfun
