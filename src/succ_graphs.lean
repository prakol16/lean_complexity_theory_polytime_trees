import data.pfun
import logic.relation
import data.fun_like.basic
import computability.turing_machine

open relation (refl_trans_gen)

structure execution (σ : Type*) :=
(next : σ →. option σ)
(start : σ)

namespace execution
variables {σ τ : Type*}

def states (f : execution σ) : set σ :=
{s | refl_trans_gen (λ x y, some y ∈ f.next x) f.start s}

@[elab_as_eliminator]
theorem induction {P : σ → Prop} (f : execution σ) (base : P f.start)
  (step : ∀ ⦃x y⦄, P x → some y ∈ f.next x → P y) {x : σ} (hx : x ∈ f.states) : P x :=
by { induction hx with _ _ _ h ih, { assumption, }, { exact step ih h, } }


structure hom (f : execution σ) (g : execution τ) :=
(to_fun : σ → τ)
(dom_of : ∀ ⦃x⦄, x ∈ f.states → (g.next (to_fun x)).dom → (f.next x).dom)
(map_fun : ∀ ⦃x⦄ ⦃y : option σ⦄, x ∈ f.states → y ∈ f.next x → y.map to_fun ∈ g.next (to_fun x))
(start : to_fun f.start = g.start)

variables (f : execution σ)

def eval : part σ :=
pfun.fix (λ s, (f.next s).map (λ x, x.elim (sum.inl s) sum.inr)) f.start

-- @[elab_as_eliminator]
-- theorem eval_induction {P : σ → Prop} {y} (f : execution σ) (hf : y ∈ f.eval)
--   (base : P y) (step : ∀ ⦃x y'⦄, )

end execution

