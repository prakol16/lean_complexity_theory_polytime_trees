import tactic.core
import tactic.tidy
import tactic.show_term

def ptree : Type := sorry

class pencodable (α : Type*) :=
(encode : α → ptree)
(decode : ptree → α)
/- (other prop's omitted) -/

section
variables {α β γ δ ε : Type*} [pencodable α] [pencodable β] [pencodable γ] [pencodable δ] [pencodable ε]

instance : pencodable (α × β) := sorry

def polytime_fun (f : α → β) : Prop := sorry

lemma polytime_fun.id : polytime_fun (@id α) := sorry
lemma polytime_fun.const (y : β) : polytime_fun (λ (_ : α), y) := sorry
lemma polytime_fun.comp {f : β → γ} {g : α → β} : polytime_fun f → polytime_fun g → polytime_fun (f ∘ g) := sorry
lemma polytime_fun.pair {f : α → β} {g : α → γ} : polytime_fun f → polytime_fun g → polytime_fun (λ x, (f x, g x)) := sorry
lemma polytime_fun.fst : polytime_fun (@prod.fst α β) := sorry
lemma polytime_fun.snd : polytime_fun (@prod.snd α β) := sorry

def polytime_fun₂ (f : α → β → γ) : Prop := polytime_fun (function.uncurry f)

def polytime_fun₃ (f : α → β → γ → δ) : Prop :=
polytime_fun (λ x : α × β × γ, f x.1 x.2.1 x.2.2)

lemma polytime_fun.comp₂ {f : α → β → γ} {g : δ → α} {h : δ → β}
  (hf : polytime_fun₂ f) (hg : polytime_fun g) (hh : polytime_fun h) :
  polytime_fun (λ x, f (g x) (h x)) :=
polytime_fun.comp hf (polytime_fun.pair hg hh)

lemma polytime_fun.comp₃ {f : α → β → γ → δ} {g₁ : ε → α} {g₂ : ε → β} {g₃ : ε -> γ}
  (hf : polytime_fun₃ f) (hg₁ : polytime_fun g₁) (hg₂ : polytime_fun g₂) (hg₃ : polytime_fun g₃) :
  polytime_fun (λ x, f (g₁ x) (g₂ x) (g₃ x)) :=
polytime_fun.comp hf (polytime_fun.pair hg₁ (polytime_fun.pair hg₂ hg₃))

end

section

@[user_attribute]
meta def polyfun : user_attribute :=
{ name := `polyfun,
  descr := "lemmas usable to prove polynomial time" }

attribute [polyfun]
  polytime_fun.id
  polytime_fun.const
  polytime_fun.pair
  polytime_fun.fst
  polytime_fun.snd

@[polyfun]
lemma polytime_fun.id' {α} [pencodable α] : polytime_fun (λ x : α, x) := polytime_fun.id

namespace tactic

meta def polytime_fun_lemmas : list name :=
[``polytime_fun, ``polytime_fun₂, ``polytime_fun₃]

meta def polytime_fun_comp_lemmas : list name :=
[``polytime_fun.comp, ``polytime_fun.comp₂, ``polytime_fun.comp₃]

meta def unfold_polytime (md : transparency) : tactic unit :=
do dunfold_target (``function.uncurry :: polytime_fun_lemmas.tail),
   try dsimp_target

-- In order to help resolve polytime_fun of propositions (which are converted to bool's)
meta def simp_to_bool : tactic unit :=
`[simp only [bool.to_bool_not, bool.to_bool_and, bool.to_bool_or, bool.to_bool_coe]]

/--
 Tries to infer if the given expression is a real argument by testing
 if it has a `pencodable` instance on it. TODO: make faster. Does this need
 to do a full instance search?
-/
meta def is_polycodable (e : expr) : tactic bool :=
(do
   e' ← infer_type e,
   cache ← mk_instance_cache e',
   (cache', s) ← instance_cache.get cache ``pencodable,
   return tt) <|> (return ff)

/-- Given an expression of the form `polytime_fun (f x₁ x₂ ... xₙ)`, tries to infer `n`,
   the number of arguments. -/
meta def get_num_params : tactic ℕ :=
do `(polytime_fun %%s) ← target,
    guard s.is_lambda,
    mv ← mk_meta_var s.binding_domain,
    e ←  instantiate_mvars (s.instantiate_lambdas [mv]),
    f ← mfilter is_polycodable e.get_app_args,
    return f.length

/--
  Given a goal of the form `⊢ polytime_fun (λ x, f (g₁ x) (g₂ x) ... (gₙ x))`
  tries to apply the corresponding composition rule to produce
  `⊢ polytime_funₙ f`, `⊢ polytime_fun g₁`, ..., `⊢ polytime_fun gₙ`
-/
meta def apply_polyfun.comp (md : transparency) : tactic ℕ :=
do fail_if_success `[exact polytime_fun.const _],
   fail_if_success (to_expr ``(polytime_fun.pair) >>= λ e, apply e {md := md}),
   old_goal ← target,
   n ← get_num_params, guard (0 < n ∧ n ≤ polytime_fun_lemmas.length),
   s ← resolve_name (polytime_fun_comp_lemmas.inth (n-1)),
   s' ← to_expr s,
   apply s' {md := md},
   try `[ any_goals { apply_instance, } ], -- why is this necessary??
   /-
    - If the target is md-definitionally equal to what it used to be, up to
    - unfolding of polytime_fun₂, polytime_fun₃ etc., then no real progress has been made
    - EXCEPT if the goal can be immediately solved by apply_rules.
    - This last check is important because if we have something like
    - `⊢ polytime_fun (λ x : α × β, f x.1 x.2)`, and `polytime_fun₂ f` is a `polyfun` lemma,
    - even though this goal is definitionally equal to `polytime_fun₂ f`, `apply_rules` would not
    - find it at the `reducible` setting. Therefore, this will get reduced to
    - `⊢ polytime_fun₂ f`, `⊢ polytime_fun (λ x : α × β, x.1)`, and `⊢ polytime_fun (λ x : α × β, x.2)`.
    - It looks like no progress has been made, but because we can immediately solve `polytime_fun₂ f`, we continue to advance.

    - We need to check for definitional equality up to `unfold_polytime` because otherwise we get caught in a loop
    - where it looks like we make progress even though we don't. If we have the goal `⊢ polytime_fun (λ x, f x.1 x.2)`,
    - this gets reduced to `⊢ polytime_fun₂ f`, ... as before. If `f` is not actually polytime, it seems like we make progress
    - if we do not unfold `polytime_fun₂`, but `polytime_fun₂` will just be unfolded back to `polytime_fun (λ x, f x.1 x.2)` before
    - `apply_polyfun.comp` is called, causing a loop.

    - This check replaces the check to exclude `id` of the `continuity` tactic.
   -/
   (fail_if_success (unfold_polytime md >> target >>= λ t, unify t old_goal md)) <|>
    focus1 (apply_rules [] [``polyfun] 50 { md := md } >> done),
  return (n-1)

meta def polyfun_tactics (md : transparency := reducible) : list (tactic string) :=
[
  apply_rules [] [``polyfun] 50 { md := md }
                        >> pure "apply_rules with polyfun",
  unfold_polytime md >> pure "dunfold_target polytime_fun_lemmas.tail",
  simp_to_bool >> pure "simp only [bool.to_bool_not, bool.to_bool_and, bool.to_bool_or]",
  apply_polyfun.comp md >>= λ n, pure ("apply " ++ (to_string $ polytime_fun_comp_lemmas.inth (n-1)))
]

namespace interactive
setup_tactic_parser

meta def polyfun
  (bang : parse $ optional (tk "!")) (trace : parse $ optional (tk "?")) (cfg : tidy.cfg := {}) :
  tactic unit :=
let md              := if bang.is_some then semireducible else reducible,
    polyfun_core := tactic.tidy { tactics := polyfun_tactics md, ..cfg },
    trace_fn        := if trace.is_some then show_term else id in
trace_fn polyfun_core


end interactive

end tactic

end

section
instance : pencodable ℕ := sorry

@[polyfun]
lemma polytime_fun.nat_add : polytime_fun₂ ((+) : ℕ → ℕ → ℕ) := sorry

example : polytime_fun₃ (λ (a b c : ℕ), a + b + c) := by polyfun
example : polytime_fun (λ (n : ℕ), (n, n + n, n + n + n)) := by polyfun



end
