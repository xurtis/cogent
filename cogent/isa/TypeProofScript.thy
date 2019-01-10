theory TypeProofScript
  imports ContextTrackingTyping TermPatternAntiquote Data
begin

declare [[ML_debugger = true]]

\<comment> \<open>
  Generates the actions the tactic should take, ahead of time, to cut down on processing time.

  Basically a rewrite of the intro rules, to hopefully make things faster
\<close>

ML {*

datatype Action = Resolve of thm | Lookup of string

fun gen_script_ttyping @{term_pat "Var ?i"} =
  Tree {value = Resolve @{thm ttyping_var}, branches = [Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "AFun ?f ?ts"} =
  Tree {value = Resolve @{thm ttyping_afun}, branches =
    [Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "Fun ?f ?ts"} =
  Tree {value = Resolve @{thm ttyping_fun}, branches =
    [Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "App ?e1 ?e2"} =
  Tree {value = Resolve @{thm ttyping_app}, branches =
    [Leaf (), gen_script_ttyping e1, gen_script_ttyping e2]}

| gen_script_ttyping @{term_pat "Con ?ts ?tag ?x"} =
  Tree {value = Resolve @{thm ttyping_con}, branches =
    [gen_script_ttyping x, Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "Cast ?t' ?e"} =
  Tree {value = Resolve @{thm ttyping_cast}, branches = [gen_script_ttyping e, Leaf ()]}

| gen_script_ttyping @{term_pat "Tuple ?e1 ?e2"} =
  Tree {value = Resolve @{thm ttyping_tuple}, branches =
    [Leaf (), gen_script_ttyping e1, gen_script_ttyping e2]}

| gen_script_ttyping @{term_pat "Split ?e1 ?e2"} =
  Tree {value = Resolve @{thm ttyping_split}, branches =
    [Leaf (), gen_script_ttyping e1, gen_script_ttyping e2]}

| gen_script_ttyping @{term_pat "Let ?e1 ?e2"} =
  Tree {value = Resolve @{thm ttyping_let}, branches =
    [Leaf (), gen_script_ttyping e1, gen_script_ttyping e2]}

| gen_script_ttyping @{term_pat "LetBang ?is ?e1 ?e2"} =
  Tree {value = Resolve @{thm ttyping_letb}, branches =
    [Leaf (), gen_script_ttyping e1, gen_script_ttyping e2, Leaf ()]}

| gen_script_ttyping @{term_pat "Case ?e ?tag ?e1 ?e2"} =
  Tree {value = Resolve @{thm ttyping_case}, branches =
    [Leaf (), gen_script_ttyping e, Leaf (), Leaf (), gen_script_ttyping e1, gen_script_ttyping e2]}

| gen_script_ttyping @{term_pat "Esac ?e"} =
  Tree {value = Resolve @{thm ttyping_esac}, branches =
    [gen_script_ttyping e, Leaf ()]}

| gen_script_ttyping @{term_pat "If ?x ?a ?b"} =
  Tree {value = Resolve @{thm ttyping_if}, branches =
    [Leaf (), Leaf (), gen_script_ttyping x, gen_script_ttyping a, gen_script_ttyping b]}

| gen_script_ttyping @{term_pat "Prim ?oper ?args"} =
  Tree {value = Resolve @{thm ttyping_prim}, branches =
    [Leaf (), Leaf (), gen_script_ttyping_all (HOLogic.dest_list args)]}
      

| gen_script_ttyping @{term_pat "Lit ?l"} =
  Tree {value = Resolve @{thm ttyping_lit}, branches =
    [Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "Unit"} =
  Tree {value = Resolve @{thm ttyping_unit}, branches = [Leaf ()]}

| gen_script_ttyping @{term_pat "Struct ?ts ?es"} =
  Tree {value = Resolve @{thm ttyping_struct}, branches =
    [gen_script_ttyping_all (HOLogic.dest_list es), Leaf (), Leaf (), Leaf (), Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "Member ?e ?f"} =
  Tree {value = Resolve @{thm ttyping_member}, branches =
    [gen_script_ttyping e, Leaf (), Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "Take ?e ?f ?e'"} =
  Tree {value = Resolve @{thm ttyping_take}, branches =
    [Leaf (), gen_script_ttyping e, Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), gen_script_ttyping e']}

| gen_script_ttyping @{term_pat "Put ?e ?f ?e'"} =
  Tree {value = Resolve @{thm ttyping_put}, branches =
    [Leaf (), gen_script_ttyping e, Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), gen_script_ttyping e']}

| gen_script_ttyping @{term_pat "Promote ?t ?e"} =
  Tree {value = Resolve @{thm ttyping_promote}, branches =
    [gen_script_ttyping e, Leaf ()]}

| gen_script_ttyping _ = raise ERROR "Not an expression!"

and gen_script_ttyping_all (x :: xs) =
  Tree { value = Resolve @{thm ttyping_all_cons}, branches =
    [Leaf (), Leaf (), gen_script_ttyping x, gen_script_ttyping_all xs] }

| gen_script_ttyping_all [] =
  Tree { value = Resolve @{thm ttyping_all_empty}, branches = [Leaf ()] }

and gen_script_lookup_name name = Tree { value = Lookup ((HOLogic.dest_string name) handle (TERM _) => (raise ERROR "tmp D")), branches = [] }

fun gen_script @{term_pat "ttyping _ _ (TyTrFun ?n, _) _ _"} = gen_script_lookup_name n
| gen_script @{term_pat "ttyping _ _ _ ?expr _"} = gen_script_ttyping expr
| gen_script @{term_pat "ttyping_all _ _ _ ?es _"} =
  gen_script_ttyping_all (HOLogic.dest_list es)
| gen_script @{term_pat "ttyping_named _ _ _ ?name _ _"} = gen_script_lookup_name name
| gen_script _ = raise ERROR "Don't know how to make a script for this!"
(*
| gen_script @{term_pat "ttsplit _ _ _ _ _ _ _"}         = IntroStrat @{thms ttsplitI}
| gen_script @{term_pat "ttsplit_inner _ _ _ _ _"}       = IntroStrat @{thms ttsplit_innerI}
| gen_script @{term_pat "ttsplit_bang _ _ _ _ _ _ _ _"}  = IntroStrat @{thms ttsplit_bangI}
| gen_script @{term_pat "ttsplit_triv _ _ _ _ _"}        = IntroStrat @{thms ttsplit_trivI}
| gen_script @{term_pat "tsk_split_comp _ _ _ _ _"}      = IntroStrat @{thms tsk_split_comp.intros}
| gen_script @{term_pat "weakening _ _ _"}               = IntroStrat @{thms weakening_cons weakening_nil}
| gen_script @{term_pat "weakening_comp _ _ _"}          = IntroStrat @{thms weakening_comp.intros}
| gen_script @{term_pat "is_consumed _ _"}               = IntroStrat @{thms weakening_cons weakening_nil}
| gen_script _ = Tree {value = UnknownStrat, branches = []}
*)

*}

end