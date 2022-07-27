import polycodable_init

@[user_attribute]
meta def polyfun : user_attribute :=
{ name := `polyfun,
  descr := "lemmas usable to prove polynomial time" }

attribute [polyfun]
  polytime_fun.id
  polytime_fun.const

namespace tactic

meta def polytime_fun_lemmas : list name :=
[``polytime_fun, ``polytime_fun₂, ``polytime_fun₃]

meta def polytime_fun_comp_lemmas : list name :=
[``polytime_fun.comp, ``polytime_fun.comp₂, ``polytime_fun.comp₃]

meta def unfold_polytime (md : transparency) : tactic unit :=
do dunfold_target (``function.uncurry :: polytime_fun_lemmas.tail),
   try dsimp_target, skip

-- In order to help resolve polytime_fun of propositions (which are converted to bool's)
meta def simp_to_bool : tactic unit :=
`[simp only [bool.to_bool_not, bool.to_bool_and, bool.to_bool_or, bool.to_bool_coe]]

-- Please help, idk how to write tactics
meta def is_polycodable (e : expr) : tactic bool :=
(do
   e' ← infer_type e,
   cache ← mk_instance_cache e',
   (cache', s) ← instance_cache.get cache ``polycodable,
   return tt) <|> (return ff)

meta def get_num_params : tactic ℕ :=
do `(polytime_fun %%s) ← tactic.target,
    guard s.is_lambda,
    mv ← mk_meta_var s.binding_domain,
    e ←  instantiate_mvars (s.instantiate_lambdas [mv]),
    f ← mfilter is_polycodable e.get_app_args,
    return f.length

meta def apply_polyfun.comp (md : transparency) : tactic ℕ :=
do fail_if_success `[exact polytime_fun.const _],
   fail_if_success (to_expr ``(polytime_fun.pair) >>= λ e, apply e {md := md}),
   n ← get_num_params, guard (0 < n ∧ n ≤ polytime_fun_lemmas.length),
   s ← resolve_name (polytime_fun_comp_lemmas.inth (n-1)),
   s' ← to_expr s,
   apply s' {md := md},
   when (n = 1) (fail_if_success `[swap, exact polytime_fun.id]),
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

section

attribute [polyfun] 
  polytime_fun.fst
  polytime_fun.snd
  polytime_fun.pair
  polytime_fun.node
  polytime_fun.polytime_code
  polytime_fun.ptree_left
  polytime_fun.ptree_right
  polytime_fun.encode
  polytime_fun.decode'
@[polyfun]
lemma polytime_fun.id' {α} [polycodable α] : polytime_fun (λ x : α, x) := polytime_fun.id

end
