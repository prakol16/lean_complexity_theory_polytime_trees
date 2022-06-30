import data.list.basic
import code

def recursion {α β γ : Type*} (pre : α → β × list α) (post : β × list γ → γ)
  (wff : ∀ t, ((pre t).2.map sizeof).sum < sizeof t) : α → γ
| x := post ((pre x).1, (pre x).2.map (λ y, have wf : sizeof y < sizeof x := sorry, recursion y))
