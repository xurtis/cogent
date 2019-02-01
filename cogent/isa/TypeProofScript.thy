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

fun gen_script_ttyping @{term_pat "Var _"} =
  Tree {value = Resolve @{thm ttyping_var}, branches = [Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "AFun _ _"} =
  Tree {value = Resolve @{thm ttyping_afun}, branches =
    [Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "Fun _ _"} =
  Tree {value = Resolve @{thm ttyping_fun}, branches =
    [Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "App ?e1 ?e2"} =
  Tree {value = Resolve @{thm ttyping_app}, branches =
    [Leaf (), gen_script_ttyping e1, gen_script_ttyping e2]}

| gen_script_ttyping @{term_pat "Con _ _ ?x"} =
  Tree {value = Resolve @{thm ttyping_con}, branches =
    [gen_script_ttyping x, Leaf (), Leaf (), Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "Cast _ ?e"} =
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

| gen_script_ttyping @{term_pat "LetBang _ ?e1 ?e2"} =
  Tree {value = Resolve @{thm ttyping_letb}, branches =
    [Leaf (), gen_script_ttyping e1, gen_script_ttyping e2, Leaf ()]}

| gen_script_ttyping @{term_pat "Case ?e _ ?e1 ?e2"} =
  Tree {value = Resolve @{thm ttyping_case}, branches =
    [Leaf (), gen_script_ttyping e, Leaf (), Leaf (), gen_script_ttyping e1, gen_script_ttyping e2]}

| gen_script_ttyping @{term_pat "Esac ?e"} =
  Tree {value = Resolve @{thm ttyping_esac}, branches =
    [gen_script_ttyping e, Leaf ()]}

| gen_script_ttyping @{term_pat "If ?x ?a ?b"} =
  Tree {value = Resolve @{thm ttyping_if}, branches =
    [Leaf (), Leaf (), gen_script_ttyping x, gen_script_ttyping a, gen_script_ttyping b]}

| gen_script_ttyping @{term_pat "Prim _ ?args"} =
  Tree {value = Resolve @{thm ttyping_prim}, branches =
    [Leaf (), Leaf (), gen_script_ttyping_all (HOLogic.dest_list args)]}
      

| gen_script_ttyping @{term_pat "Lit _"} =
  Tree {value = Resolve @{thm ttyping_lit}, branches =
    [Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "SLit _"} =
  Tree {value = Resolve @{thm ttyping_slit}, branches =
    [Leaf ()]}

| gen_script_ttyping @{term_pat "Unit"} =
  Tree {value = Resolve @{thm ttyping_unit}, branches = [Leaf ()]}

| gen_script_ttyping @{term_pat "Struct _ ?es"} =
  Tree {value = Resolve @{thm ttyping_struct}, branches =
    [gen_script_ttyping_all (HOLogic.dest_list es), Leaf (), Leaf (), Leaf (), Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "Member ?e _"} =
  Tree {value = Resolve @{thm ttyping_member}, branches =
    [gen_script_ttyping e, Leaf (), Leaf (), Leaf ()]}

| gen_script_ttyping @{term_pat "Take ?e _ ?e'"} =
  Tree {value = Resolve @{thm ttyping_take}, branches =
    [Leaf (), gen_script_ttyping e, Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), gen_script_ttyping e']}

| gen_script_ttyping @{term_pat "Put ?e _ ?e'"} =
  Tree {value = Resolve @{thm ttyping_put}, branches =
    [Leaf (), gen_script_ttyping e, Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), Leaf (), gen_script_ttyping e']}

| gen_script_ttyping @{term_pat "Promote _ ?e"} =
  Tree {value = Resolve @{thm ttyping_promote}, branches =
    [gen_script_ttyping e, Leaf ()]}

| gen_script_ttyping t = raise ERROR (@{make_string} t ^ " is not a recognised expression!")

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




(*
lemma type_wellformed_intros:

  "\<And>K ts s. \<lbrakk> distinct (map fst ts) ; list_all (\<lambda>x. type_wellformed_pretty K (fst (snd x))) ts \<rbrakk> \<Longrightarrow> type_wellformed_pretty K (TRecord ts s)"
  "\<And>K. type_wellformed_pretty K TUnit"

*)

fun gen_script_wellformed @{term_pat "TVar _"} =
  Tree {value = Resolve @{thm type_wellformed_intros(1)}, branches = [Leaf ()]}

| gen_script_wellformed @{term_pat "TVarBang _"} =
  Tree {value = Resolve @{thm type_wellformed_intros(2)}, branches = [Leaf ()]}

| gen_script_wellformed @{term_pat "TCon _ ?ts _"} =
  Tree {value = Resolve @{thm type_wellformed_intros(3)}, branches =
    [gen_script_wellformed_all (HOLogic.dest_list ts)]}

| gen_script_wellformed @{term_pat "TFun ?ta ?tb"} =
  Tree {value = Resolve @{thm type_wellformed_intros(4)}, branches =
    [gen_script_wellformed ta, gen_script_wellformed tb]}

| gen_script_wellformed @{term_pat "TPrim _"} =
  Tree {value = Resolve @{thm type_wellformed_intros(5)}, branches = []}

| gen_script_wellformed @{term_pat "TSum ?ts"} =
  Tree {value = Resolve @{thm type_wellformed_intros(6)}, branches =
    [Leaf (), gen_script_wellformed_all
      (map (HOLogic.dest_prod #> snd #> HOLogic.dest_prod #> fst) (HOLogic.dest_list ts))]}

| gen_script_wellformed @{term_pat "TProduct ?t1 ?t2"} =
  Tree {value = Resolve @{thm type_wellformed_intros(7)}, branches = [gen_script_wellformed t1, gen_script_wellformed t2]}

| gen_script_wellformed @{term_pat "TRecord ?ts _"} =
  Tree {value = Resolve @{thm type_wellformed_intros(8)}, branches =
    [Leaf (), gen_script_wellformed_all
      (map (HOLogic.dest_prod #> snd #> HOLogic.dest_prod #> fst) (HOLogic.dest_list ts))]}

| gen_script_wellformed @{term_pat "TUnit"} =
  Tree {value = Resolve @{thm type_wellformed_intros(9)}, branches = []}

| gen_script_wellformed t = raise ERROR (@{make_string} t ^ " is not a recognised type!")

and gen_script_wellformed_all (x :: xs) =
  Tree { value = Resolve @{thm list_all_cons}, branches =
    [gen_script_wellformed x, gen_script_wellformed_all xs] }

| gen_script_wellformed_all [] =
  Tree { value = Resolve @{thm list_all_nil}, branches = [] }



*}

end