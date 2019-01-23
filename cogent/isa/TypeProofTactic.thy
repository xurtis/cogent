theory TypeProofTactic
  imports ContextTrackingTyping TermPatternAntiquote Data TypeProofScript
begin

declare [[ML_debugger = true]]

ML {*

fun simp_term ctxt =
    Thm.cterm_of ctxt
    #> Simplifier.full_rewrite ctxt
    #> Thm.prop_of
    #> Logic.dest_equals
    #> snd

type cogent_fun_info = { xidef : thm list, funs: thm list, absfuns: thm list }

fun cogent_fun_info_allsimps { xidef : thm list, funs: thm list, absfuns: thm list }
  = xidef @ funs @ absfuns

fun add_simps thms ctxt = fold Simplifier.add_simp thms ctxt

datatype GoalStrategy = IntroStrat of thm list | LookupStrat of string

fun goal_get_intros @{term_pat "ttyping_named _ _ _ ?name _ _"} =
  name         
    |> simp_term (add_simps @{thms char_of_def} @{context}) (* strings can have functions in them, which need to be evaluated for dest_string to work *)
    |> HOLogic.dest_string
    |> LookupStrat
    |> SOME
| goal_get_intros @{term_pat "ttsplit _ _ _ _ _ _"}           = IntroStrat @{thms ttsplitI} |> SOME
| goal_get_intros @{term_pat "ttsplit_inner _ _ _ _ _"}       = IntroStrat @{thms ttsplit_innerI} |> SOME
| goal_get_intros @{term_pat "ttsplit_bang _ _ _ _ _ _ _"}    = IntroStrat @{thms ttsplit_bangI} |> SOME
| goal_get_intros @{term_pat "ttsplit_triv _ _ _ _ _"}        = IntroStrat @{thms ttsplit_trivI} |> SOME
| goal_get_intros @{term_pat "tsk_split_comp _ _ _ _ _"}      = IntroStrat @{thms tsk_split_comp.intros} |> SOME
| goal_get_intros @{term_pat "weakening _ _ _"}               = IntroStrat @{thms weakening_cons weakening_nil} |> SOME
| goal_get_intros @{term_pat "weakening_comp _ _ _"}          = IntroStrat @{thms weakening_comp.intros} |> SOME
| goal_get_intros @{term_pat "is_consumed _ _"}               = IntroStrat @{thms is_consumed_cons is_consumed_nil} |> SOME
| goal_get_intros _ = NONE


datatype tac_types = Simp of thm list | Force of thm list | FastForce of thm list | UnknownTac

(* TODO the fact we need to specify all the possible misc goal patterns is a bit of a mess.
  Maybe just default to force with an expanded simpset when we don't know what to do?
  (the problem with this approach would be possible looping)
  ~ v.jackson / 2018.12.04 *)

fun goal_type_of_term @{term_pat "Cogent.kinding _ _ _"}      = SOME (Force @{thms kinding_defs})
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
| goal_type_of_term @{term_pat "subtyping _ _ _"}             = SOME (Force @{thms subtyping_simps})
| goal_type_of_term @{term_pat "upcast_valid _ _"}            = SOME (Force @{thms upcast_valid.simps})
| goal_type_of_term _                                         = NONE

(* TODO n.b. this approach only works because we never encounter a proof like
  \<open>False \<Longrightarrow> False\<close> where we can't show the premise is true (and thus vacuous + removable).
  I don't think we should encounter this, but make certain we don't.
  ~ v.jackson / 2018.12.04 *)

fun strip_trueprop @{term_pat "HOL.Trueprop ?t"} = t
| strip_trueprop _ = raise ERROR "strip_trueprop was passed something which isn't a Trueprop"

fun reduce_goal _ UnknownTac goal =
  raise ERROR ("Don't know what to do with: " ^ @{make_string} (Thm.cprem_of goal 1))
| reduce_goal ctxt (Simp thms) goal =
  SOLVED' (Simplifier.asm_full_simp_tac (add_simps thms ctxt)) 1 goal
| reduce_goal ctxt (Force thms) goal =
   SOLVED' (force_tac (add_simps thms ctxt)) 1 goal
| reduce_goal ctxt (FastForce thms) goal =
   SOLVED' (fast_force_tac (add_simps thms ctxt)) 1 goal


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
  failed : proof_status rtree (* the subgoal which failed *)
}
| ProofUnexpectedTerm of thm

fun goal_cleanup_tac ctxt =
  Simplifier.asm_full_simp_tac
    (add_simps @{thms Cogent.empty_def} ctxt)
    1

(* trace the last unsolved subgoal *)
fun trace_typeproof (Tree { value = ProofFailed { goal = _, failed = failed_subgoal }, branches = _ }) =
  trace_typeproof failed_subgoal
| trace_typeproof (Tree { value = ProofUnexpectedTerm goal, branches = _ } : proof_status rtree) =
  (@{print tracing} goal ; ())
| trace_typeproof (Tree { value = _, branches = _ } : proof_status rtree) = ()



fun reduce_goal' ctxt cogent_fun_info goal t_subgoal =
  let
    val goal_type =
      (case goal_type_of_term (strip_trueprop t_subgoal) of
        SOME goal_type => goal_type
      | NONE => raise ERROR ("(solve_typeproof) unknown goal type for: " ^ @{make_string} (Thm.cprem_of goal 1)))
    val applytac =
      reduce_goal (add_simps (cogent_fun_info_allsimps cogent_fun_info) ctxt) goal_type goal
  in
    case Seq.pull applytac of
      SOME (goal', _) => goal'                         
    | NONE => raise ERROR ("(solve_typeproof) failed to solve subgoal: " ^ @{make_string} (Thm.cprem_of goal 1))
  end


(* solve misc subgoal is for where we want to solve subgoals without generating a tree for every subexpression *)
fun solve_misc_goal ctxt cogent_fun_info goal (IntroStrat intros) =
    let
      val goal =
        goal
          |> goal_cleanup_tac ctxt
          |> Seq.pull
          |> (the #> fst)
      val goal'_seq = resolve_tac ctxt intros 1 goal
      val goal' = case Seq.pull goal'_seq of
        SOME (goal', _) => goal'
        | NONE =>
          raise ERROR ("solve_misc_goal: failed to resolve goal " ^
             @{make_string} goal ^
             " with provided intro rule" ^
             @{make_string} intros)
    in
      solve_misc_subgoals ctxt cogent_fun_info goal'
    end
| solve_misc_goal ctxt cogent_fun_info goal (LookupStrat name) =
  let
    (* TODO this assumes things about generation *)
    val lookup_thm_name = (prefix "isa_" #> suffix "_typecorrect") name
    val lookup_thm = Proof_Context.get_thms ctxt lookup_thm_name
    val results = goal
      |> ((resolve_tac ctxt @{thms ttyping_named} 1)
        THEN (resolve_tac ctxt lookup_thm 1))
    val goal' = (case Seq.pull results of
        SOME (goal, _) => goal
      | NONE => raise ERROR ("solve_typing_goal: failed to apply named thm " ^ (@{make_string} goal)))           
    val fun_simps = (#absfuns cogent_fun_info) @ (#funs cogent_fun_info)
    val cleaned_goal =
      Conv.fconv_rule (Simplifier.full_rewrite (add_simps fun_simps ctxt)) goal'
  in
    solve_misc_subgoals ctxt cogent_fun_info cleaned_goal
  end
and solve_misc_subgoals ctxt cogent_fun_info goal =
  if Thm.no_prems goal
  then Goal.finish ctxt goal
  else
    let
      val subgoal = Thm.major_prem_of goal
    in
      case goal_get_intros (strip_trueprop subgoal) of
        SOME strat =>
          let
            val subgoal = subgoal |> Thm.cterm_of ctxt |> Goal.init
            val solved_subgoal = solve_misc_goal ctxt cogent_fun_info subgoal strat
            (* we solved the subgoal, resolve it with our goal to make the goal smaller *)
            val resolve_goal_seq = resolve_tac ctxt [solved_subgoal] 1 goal
            val goal' =
              case Seq.pull resolve_goal_seq of
                SOME (goal', _) => goal'
                | NONE =>
                  raise ERROR ("solve_misc_subgoals: failed to resolve subgoal (" ^
                              @{make_string} goal ^
                              ") with solved subgoal: " ^ @{make_string} solved_subgoal)
          in
            solve_misc_subgoals ctxt cogent_fun_info goal'
          end
        | NONE =>
          reduce_goal' ctxt cogent_fun_info goal subgoal
            |> solve_misc_subgoals ctxt cogent_fun_info
    end


(* solve_typeproof takes a proposition term and solves it by recursively solving the term tree *)
fun solve_ttyping ctxt cogent_fun_info (Tree { value = Resolve thm, branches = hints }) t_start : proof_status rtree =
  let
    val goal =
         Thm.cterm_of ctxt t_start
      |> Goal.init
      |> Simplifier.simp_tac ctxt 1
      |> Seq.pull
      |> (the #> fst);
    val res = resolve_tac ctxt [thm] 1 goal
    val goal' =
      case Seq.pull res of
        SOME (goal', _) => goal'
        | NONE => raise ERROR "solve_ttyping: failed to resolve with hinted intro rule!"
  in
     solve_subgoals ctxt cogent_fun_info goal' hints []
  end
| solve_ttyping _ _ _ _ = error "solve got bad hints"
and solve_subgoals ctxt cogent_fun_info goal (hint :: hints) solved_subgoals_rev : proof_status rtree = 
  let
    val t_subgoal = Thm.major_prem_of goal
    val subgoal = t_subgoal |> Thm.cterm_of ctxt |> Goal.init
  in
    (case hint of
      (Leaf _) =>
        (case goal_get_intros (strip_trueprop t_subgoal) of
          (SOME strat) =>
            let
              val thm_subgoal = solve_misc_goal ctxt cogent_fun_info subgoal strat
              val solved_subgoal = Tree { value = ProofDone thm_subgoal, branches = [] }
            in
              solve_resolve_with_goal ctxt cogent_fun_info goal solved_subgoal hints solved_subgoals_rev
            end
          | NONE =>
            let
              val goal' = reduce_goal' ctxt cogent_fun_info goal t_subgoal
            in
              solve_subgoals ctxt cogent_fun_info goal' hints solved_subgoals_rev
            end)
    | (Tree _) =>
      (let
        val solved_subgoal = solve_ttyping ctxt cogent_fun_info hint t_subgoal
      in
        solve_resolve_with_goal ctxt cogent_fun_info goal solved_subgoal hints solved_subgoals_rev
      end))
  end
| solve_subgoals ctxt _ goal [] solved_subgoals_rev =
  Tree { value = ProofDone (Goal.finish ctxt goal), branches = rev solved_subgoals_rev }
and solve_resolve_with_goal ctxt cogent_fun_info goal solved_subgoal hints solved_subgoals_rev =
  (* we solved the subgoal, resolve it with our goal to make the goal smaller *)
  (case tree_value solved_subgoal of
    ProofDone thm_subgoal =>
      let
        val goal' =
          case Seq.pull (resolve_tac ctxt [thm_subgoal] 1 goal) of
            SOME (thm_soln, _) => thm_soln
          | NONE => (* this shouldn't happen! *)
            raise ERROR ("failed to resolve subgoal (" ^ @{make_string} goal ^ ") with solved subgoal: " ^ (@{make_string} thm_subgoal))
      in
        solve_subgoals ctxt cogent_fun_info goal' hints (solved_subgoal :: solved_subgoals_rev)
      end
    | _ => (* if the subgoal fails, the goal fails too *)
      Tree { value = ProofFailed { goal = goal, failed = solved_subgoal }, branches = rev solved_subgoals_rev })


fun get_typing_tree3 ctxt cogent_fun_info f script : thm rtree =
  let val abbrev_defs = Proof_Context.get_thms ctxt "abbreviated_type_defs"
                        handle ERROR _ => [];
      (* generate a simpset of all the definitions of the `f` function, type, and typetree *)
      val defs = maps (Proof_Context.get_thms ctxt)
                   (map (prefix f) ["_def", "_type_def", "_typetree_def"] @ ["replicate_unfold"])
                 @ abbrev_defs;
      val main_goal = (Syntax.read_term ctxt
         ("Trueprop (\<Xi>, fst " ^ f ^ "_type, (" ^ f ^ "_typetree, [Some (fst (snd " ^ f ^ "_type))])" ^
          "            T\<turnstile> " ^ f ^ " : snd (snd " ^ f ^ "_type))"));
  in
    solve_ttyping (fold Simplifier.add_simp defs ctxt) cogent_fun_info script main_goal
    |> rtree_map (fn v =>
      case v of
        ProofDone tr => tr
      | _ => error ("get_typing_tree: failed for function " ^ f))
  end
*}

end