theory TypeProofTactic
  imports ContextTrackingTyping TermPatternAntiquote Data
begin

declare [[ML_debugger = true]]

ML {*

fun add_simps thms ctxt = fold Simplifier.add_simp thms ctxt

fun goal_get_intros @{term_pat "ttyping _ _ _ _ _"}          = SOME @{thms ttyping_ttyping_all_ttyping_named.intros}
| goal_get_intros @{term_pat "ttyping_all _ _ _ _ _"}        = SOME @{thms ttyping_ttyping_all_ttyping_named.intros}
(* TODO need to do something more for ttyping_named *)
| goal_get_intros @{term_pat "ttyping_named _ _ _ _ _ _"}    = SOME @{thms ttyping_ttyping_all_ttyping_named.intros}
| goal_get_intros @{term_pat "ttsplit _ _ _ _ _ _ _"}        = SOME @{thms ttsplitI}
| goal_get_intros @{term_pat "ttsplit_inner _ _ _ _ _"}      = SOME @{thms ttsplit_innerI}
| goal_get_intros @{term_pat "ttsplit_bang _ _ _ _ _ _ _ _"} = SOME @{thms ttsplit_bangI}
| goal_get_intros @{term_pat "tsk_split_comp _ _ _ _ _"}     = SOME @{thms tsk_split_comp.intros}
| goal_get_intros @{term_pat "weakening _ _ _"}              = SOME @{thms weakening_cons weakening_nil}
| goal_get_intros @{term_pat "weakening_comp _ _ _"}         = SOME @{thms weakening_comp.intros}
| goal_get_intros @{term_pat "is_consumed _ _"}              = SOME @{thms weakening_cons weakening_nil}
| goal_get_intros _ = NONE


datatype tac_types = Simp of thm list | Force of thm list | Unknown

(* TODO the fact we need to specify all the possible misc goal patterns is a bit of a mess.
  Maybe just default to force with an expanded simpset when we don't know what to do?
  (the problem with this approach would be possible looping)
  ~ v.jackson / 2018.12.04 *)

fun goal_type_of_term @{term_pat "ttsplit_triv _ _ _ _ _"}    = SOME (Force @{thms ttsplit_triv_def})
| goal_type_of_term @{term_pat "Cogent.kinding _ _ _"}        = SOME (Force @{thms kinding_defs})
| goal_type_of_term @{term_pat "is_consumed _ _"}             = SOME (Simp @{thms Cogent.is_consumed_def Cogent.empty_def Cogent.singleton_def})
| goal_type_of_term @{term_pat "type_wellformed_pretty _ _"}  = SOME (Simp [])
| goal_type_of_term @{term_pat "_ = _"}                       = SOME (Force @{thms Cogent.empty_def})
| goal_type_of_term @{term_pat "_ \<noteq> _"}                       = SOME (Force @{thms Cogent.empty_def})
| goal_type_of_term @{term_pat "Ex _"}                        = SOME (Force [])
| goal_type_of_term @{term_pat "All _"}                       = SOME (Force [])
| goal_type_of_term @{term_pat "_ \<and> _"}                       = SOME (Force [])
| goal_type_of_term @{term_pat "_ \<or> _"}                       = SOME (Force [])
| goal_type_of_term @{term_pat "_ < _"}                       = SOME (Force [])
| goal_type_of_term @{term_pat "_ \<in> _"}                       = SOME (Force [])
| goal_type_of_term @{term_pat "distinct _"}                  = SOME (Force [])
| goal_type_of_term @{term_pat "list_all _ _"}                = SOME (Force [])
| goal_type_of_term @{term_pat "list_all2 _ _ _"}             = SOME (Force [])
| goal_type_of_term _                                         = NONE

(* TODO n.b. this approach only works because we never encounter a proof like
  \<open>False \<Longrightarrow> False\<close> where we can't show the premise is true (and thus vacuous + removable).
  I don't think we should encounter this, but make certain we don't.
  ~ v.jackson / 2018.12.04 *)

fun strip_trueprop @{term_pat "HOL.Trueprop ?t"} = t
| strip_trueprop _ = raise ERROR "strip_trueprop was passed something which isn't a Trueprop"

fun reduce_goal _ _ Unknown goal =
  raise ERROR ("Don't know what to do with: " ^ @{make_string} (Thm.cprem_of goal 1))
| reduce_goal ctxt _ (Simp thms) goal =
  SOLVED' (Simplifier.asm_full_simp_tac (add_simps thms ctxt)) 1 goal
| reduce_goal ctxt absfun_defs (Force thms) goal =
   SOLVED' (force_tac (add_simps (thms @ absfun_defs) ctxt)) 1 goal


datatype proof_status =
  ProofDone of thm
(*
need this eventually for branching
(* a subgoal is a goal which we apply to the main goal after it gets solved, to eliminate schemantic
  variables in the goal for future subgoals *)
| ProofSubgoal of thm
*)
| ProofFailed of {
  goal : thm, (* the overall goal of the current proof *)
  failed : proof_status tree (* the subgoal which failed *)
}
| ProofUnexpectedTerm of thm

fun goal_cleanup_tac ctxt =
  Simplifier.asm_full_simp_tac
    (add_simps @{thms Cogent.empty_def} ctxt)
    1

(* solve_typeproof takes a proposition term and solves it by recursively solving the term tree *)
fun solve_typeproof ctxt absfun_defs (Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $ t_rest) : proof_status tree =
  let
    val t_start = (Const ("HOL.Trueprop", @{typ "bool \<Rightarrow> prop"}) $ t_rest);
    val goal =
         Thm.cterm_of ctxt t_start
      |> Goal.init
      |> Simplifier.simp_tac ctxt 1
      |> Seq.pull
      |> (the #> fst);
  in
    case goal_get_intros t_rest of
      SOME intros =>
        let
          val cleaned_goal = goal_cleanup_tac ctxt goal |> Seq.pull |> the |> fst
          val results = resolve_tac ctxt intros 1 cleaned_goal
          (* TODO more principled handling of tactic results *)
          val goal' = (case Seq.pull results of
              SOME (goal, _) => goal
            | NONE => raise ERROR ("solve_typing_goal: failed to apply intro to " ^ (@{make_string} cleaned_goal)))
        in
          solve_typeproof_subgoals ctxt absfun_defs goal' []
        end
      | NONE =>
        Tree { value = ProofUnexpectedTerm goal, branches = [] } (* we don't know what this is! *)
  end
| solve_typeproof _ _ _ = raise ERROR "solve_typeproof was not passed a Trueprop!"
(* iteratively solve the subgoals, unifying as we go *)
and solve_typeproof_subgoals ctxt absfun_defs goal solved_subgoals_rev : proof_status tree = 
  case Thm.prems_of goal of
    (t_subgoal :: _) =>
        (case goal_get_intros (strip_trueprop t_subgoal) of
          SOME _ => (* we can solve this one recursively, make a new subgoal *)
            let
              val solved_subgoal = solve_typeproof ctxt absfun_defs t_subgoal (* solve the subgoal *)
            in
              (case tree_value solved_subgoal of
                ProofDone thm_subgoal =>
                  (* we solved the subgoal, resolve it with our goal to make the goal smaller *)
                  let
                    val goal' =
                      case Seq.pull (resolve_tac ctxt [thm_subgoal] 1 goal) of
                        SOME (thm_soln, _) => thm_soln
                      | NONE => (* this shouldn't happen! *)
                        raise ERROR ("failed to unify subgoal (" ^ @{make_string} goal ^ ") with solved subgoal: " ^ (@{make_string} thm_subgoal))
                  in
                    solve_typeproof_subgoals ctxt absfun_defs goal' (solved_subgoal :: solved_subgoals_rev)
                  end
              | _ => (* if the subgoal fails, the goal fails too *)
                Tree { value = ProofFailed { goal = goal, failed = solved_subgoal }, branches = rev solved_subgoals_rev })
            end
        | NONE =>
          let
            val goal_type =
              (case goal_type_of_term (strip_trueprop t_subgoal) of
                SOME goal_type => goal_type
              | NONE => raise ERROR ("(solve_typeproof) unknown goal type for: " ^ @{make_string} (Thm.cprem_of goal 1)))
            val goal' =
              (case Seq.pull (reduce_goal ctxt absfun_defs goal_type goal) of
                SOME (goal', _) => goal'
              | NONE => raise ERROR ("(solve_typeproof) failed to solve subgoal: " ^ @{make_string} (Thm.cprem_of goal 1)))
          in
            (* recurse with the reduced goal *)
            solve_typeproof_subgoals ctxt absfun_defs goal' solved_subgoals_rev
          end)
  (* no more subgoals, we've solved the goal *)
  | [] => Tree { value = ProofDone (Goal.finish ctxt goal), branches = rev solved_subgoals_rev }

(* trace the last unsolved subgoal *)
fun trace_typeproof (Tree { value = ProofFailed { goal = _, failed = failed_subgoal }, branches = _ }) =
  trace_typeproof failed_subgoal
| trace_typeproof (Tree { value = ProofUnexpectedTerm goal, branches = _ } : proof_status tree) =
  (@{print tracing} goal ; ())
| trace_typeproof (Tree { value = _, branches = _ } : proof_status tree) = ()



fun get_typing_tree2 ctxt absfuns f : thm tree =
  let val abbrev_defs = Proof_Context.get_thms ctxt "abbreviated_type_defs"
                        handle ERROR _ => [];
      (* generate a simpset of all the definitions of the `f` function, type, and typetree *)
      val defs = maps (Proof_Context.get_thms ctxt)
                   (map (prefix f) ["_def", "_type_def", "_typetree_def"] @ ["replicate_unfold", "\<Xi>_def"])
                 @ abbrev_defs;
      (* TODO: a little bit of a hack. Assumes we know what the prefix isabelle is going to put
               on the function names is. *)
      val absfun_defs = (map (prefix "isa_" #> suffix "_type_def") absfuns) @ [ "\<Xi>_def" ]
        |>  maps (Proof_Context.get_thms ctxt)
      val main_goal = (Syntax.read_term ctxt
         ("Trueprop (\<Xi>, fst " ^ f ^ "_type, (" ^ f ^ "_typetree, [Some (fst (snd " ^ f ^ "_type))])" ^
          "            T\<turnstile> " ^ f ^ " : snd (snd " ^ f ^ "_type))"));
  in
    solve_typeproof (fold Simplifier.add_simp defs ctxt) absfun_defs main_goal
    |> tree_map (fn v =>
      case v of
        ProofDone tr => tr
      | _ => error ("(get_typing_tree2) failed for function " ^ f))
  end
*}

end