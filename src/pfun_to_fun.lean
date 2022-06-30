import time_bound

namespace pfun

variables {α β : Type*} (f : α →. β)

def to_fun (hf : f.dom = set.univ) : α → β := λ x, (f x).get (by { change x ∈ f.dom, rw hf, trivial, })

end pfun
