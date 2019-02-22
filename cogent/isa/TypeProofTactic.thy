theory TypeProofTactic
  imports ContextTrackingTyping TermPatternAntiquote Data TypeProofScript AssocLookup
begin

(* n.b. The solving approach this tactic takes only works because we never encounter a proof like
  \<open>False \<Longrightarrow> False\<close> where we can't show the premise is true (and thus vacuous + removable).
  The rules use in typing have to be written so this doesn't happen
  ~ v.jackson / 2018.12.04 *)


(* Rewritten rules so we can avoid spurious failures due to unification *)
lemma subty_trecord':
  assumes
    "map (fst \<circ> snd) ts1 = ts1'"
    "map (fst \<circ> snd) ts2 = ts2'"
    "list_all2 (subtyping K) ts1' ts2'"
    "map fst ts1 = map fst ts2"
    "list_all2 (record_kind_subty K) ts1 ts2"
    "distinct (map fst ts1)"
    "s1 = s2"
  shows
    "K \<turnstile> TRecord ts1 s1 \<sqsubseteq> TRecord ts2 s2"
  using assms
  by (force intro: subtyping.intros simp add: list_all2_map1 list_all2_map2)

lemma subty_tsum':
  assumes
    "map (fst \<circ> snd) ts1 = ts1'"
    "map (fst \<circ> snd) ts2 = ts2'"
    "list_all2 (subtyping K) ts1' ts2'"
    "map fst ts1 = map fst ts2"
    "list_all2 variant_kind_subty ts1 ts2"
    "distinct (map fst ts1)"
  shows
    "K \<turnstile> TSum ts1 \<sqsubseteq> TSum ts2"
  using assms
  by (force intro: subtyping.intros simp add: list_all2_map1 list_all2_map2)

lemma singleton_weakening:
  "\<Gamma>' = (replicate n None)[i := Some t] \<Longrightarrow> K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>' \<Longrightarrow> K \<turnstile> \<Gamma> \<leadsto>w singleton n i t"
  by (simp add: Cogent.empty_def)

ML_file "../../l4v/tools/autocorres/mkterm_antiquote.ML"

declare [[ML_debugger = true]]

ML {*

val TIMEOUT_WARN = Time.fromMilliseconds 700
val TIMEOUT_WARN_MISC_SUBG = Time.fromMilliseconds 1000
val TIMEOUT_KILL = Time.fromMilliseconds 10000

fun rewrite_cterm ctxt =
       Simplifier.rewrite ctxt
    #> Thm.prop_of
    #> Logic.dest_equals
    #> snd

type cogent_info = { xidef : thm list, funs: thm list, absfuns: thm list, type_defs: thm list }

fun cogent_info_funandtypesimps ({ xidef, funs, absfuns, type_defs } : cogent_info)
  = funs @ absfuns @ type_defs

fun cogent_info_funsimps ({ xidef, funs, absfuns, type_defs } : cogent_info)
  = funs @ absfuns

fun cogent_info_allsimps ({ xidef, funs, absfuns, type_defs } : cogent_info)
  = xidef @ funs @ absfuns @ type_defs

datatype GoalStrategy = IntroStrat of thm list | LookupStrat of string | ResolveNetStrat of (int * thm) Net.net

(* nets *)
val subtyping_net = Tactic.build_net @{thms subtyping.intros(1-5,7,9) subty_trecord' subty_tsum'}


fun goal_get_intros @{term_pat "ttyping_named _ _ _ ?name _ _"} =
  name
    |> Thm.cterm_of @{context}
    |> rewrite_cterm (Simplifier.addsimps (@{context}, @{thms char_of_def})) (* strings can have functions in them, which need to be evaluated for dest_string to work *)
    |> HOLogic.dest_string
    |> LookupStrat
    |> SOME
| goal_get_intros @{term_pat "ttsplit _ _ _ _ _ _"}             = IntroStrat @{thms ttsplitI} |> SOME
| goal_get_intros @{term_pat "ttsplit_inner _ _ _ _ _"}         = IntroStrat @{thms ttsplit_innerI} |> SOME
| goal_get_intros @{term_pat "ttsplit_bang _ _ _ _ _ _ _"}      = IntroStrat @{thms ttsplit_bangI} |> SOME
| goal_get_intros @{term_pat "ttctxdup _ _ _ _ _"}              = IntroStrat @{thms ttctxdupI} |> SOME
| goal_get_intros @{term_pat "tsk_split_comp _ _ _ _ _"}        = IntroStrat @{thms tsk_split_comp.intros} |> SOME
| goal_get_intros @{term_pat "weakening _ _ (singleton _ _ _)"} = IntroStrat @{thms singleton_weakening} |> SOME
| goal_get_intros @{term_pat "weakening _ [] []"}               = IntroStrat @{thms weakening_nil} |> SOME
| goal_get_intros @{term_pat "weakening _ (_ # _) (_ # _)"}     = IntroStrat @{thms weakening_cons} |> SOME
| goal_get_intros @{term_pat "weakening_comp _ _ _"}            = IntroStrat @{thms weakening_comp.intros} |> SOME
| goal_get_intros @{term_pat "is_consumed _ _"}                 = IntroStrat @{thms is_consumed_cons is_consumed_nil} |> SOME
| goal_get_intros @{term_pat "subtyping _ _ _"}                 = subtyping_net |> ResolveNetStrat |> SOME
| goal_get_intros @{term_pat "list_all2 _ [] []"}               = IntroStrat @{thms list_all2_nil} |> SOME
| goal_get_intros @{term_pat "list_all2 _ (_ # _) (_ # _)"}     = IntroStrat @{thms list_all2_cons} |> SOME
(* | goal_get_intros @{term_pat "type_wellformed_pretty _ _"}    = IntroStrat @{thms type_wellformed_pretty_intros} |> SOME *)
| goal_get_intros _ = NONE


datatype tac_types = Simp of thm list | Force of thm list | UnknownTac

(* TODO the fact we need to specify all the possible misc goal patterns is a bit of a mess.
  Maybe just default to force with an expanded simpset when we don't know what to do?
  (the problem with this approach would be possible looping)
  ~ v.jackson / 2018.12.04 *)

fun goal_type_of_term @{term_pat "Cogent.kinding _ _ _"}      = SOME (Force @{thms kinding_defs type_wellformed_pretty_def})
| goal_type_of_term @{term_pat "\<Xi> _ = _"}                     = SOME (Force @{thms Cogent.empty_def})
| goal_type_of_term @{term_pat "_ = _"}                       = SOME (Force @{thms Cogent.empty_def})
| goal_type_of_term @{term_pat "_ \<noteq> _"}                       = SOME (Force @{thms Cogent.empty_def})
| goal_type_of_term @{term_pat "type_wellformed_pretty _ _"}  = SOME (Force @{thms type_wellformed_pretty_def})
| goal_type_of_term @{term_pat "Ex _"}                        = SOME (Force [])
| goal_type_of_term @{term_pat "All _"}                       = SOME (Force [])
| goal_type_of_term @{term_pat "_ \<and> _"}                       = SOME (Force [])
| goal_type_of_term @{term_pat "_ \<or> _"}                       = SOME (Force [])
| goal_type_of_term @{term_pat "_ < _"}                       = SOME (Force [])
| goal_type_of_term @{term_pat "_ \<in> _"}                       = SOME (Force [])
| goal_type_of_term @{term_pat "distinct _"}                  = SOME (Force [])
| goal_type_of_term @{term_pat "list_all _ _"}                = SOME (Force [])
| goal_type_of_term @{term_pat "list_all2 _ _ _"}             = SOME (Force @{thms subtyping_simps})
(* | goal_type_of_term @{term_pat "subtyping _ _ _"}             = SOME (Force @{thms subtyping_simps}) *)
| goal_type_of_term @{term_pat "upcast_valid _ _"}            = SOME (Force @{thms upcast_valid.simps})
| goal_type_of_term @{term_pat "is_consumed _ _"}             = SOME (Simp @{thms Cogent.is_consumed_def Cogent.empty_def Cogent.singleton_def})
| goal_type_of_term @{term_pat "record_kind_subty _ _ _"}     = SOME (Force @{thms kinding_defs type_wellformed_pretty_def})
| goal_type_of_term @{term_pat "variant_kind_subty _ _"}      = SOME (Simp [])
| goal_type_of_term _                                         = NONE

fun strip_trueprop @{term_pat "HOL.Trueprop ?t"} = t
| strip_trueprop _ = raise ERROR "strip_trueprop was passed something which isn't a Trueprop"

datatype proof_status =
  ProofDone of thm
| ProofFailed of {
  goal : thm, (* the overall goal of the current proof *)
  failed : proof_status rtree (* the subgoal which failed *)
}
| ProofUnexpectedTerm of thm

fun reduce_goal ctxt cogent_info goal t_subgoal =
  let
    val timing_leaf = Timing.start ()
    val goal_type =
      (case t_subgoal |> Thm.term_of |> strip_trueprop |> goal_type_of_term of
        SOME goal_type => goal_type
      | NONE => raise ERROR ("(solve_typeproof) unknown goal type for: " ^ @{make_string} (Thm.cprem_of goal 1)))
    val (thms, tac) =
      case goal_type of
        Simp thms => (thms, Simplifier.simp_tac)
      | Force thms => (thms, fast_force_tac)
      | UnknownTac => raise ERROR ("Don't know what to do with: " ^ @{make_string} (Thm.cprem_of goal 1))
    val applytac =
      (Timeout.apply TIMEOUT_KILL (
        SOLVED' (
          Simplifier.rewrite_goal_tac ctxt (@{thms assoc_lookup_simps} @ #xidef cogent_info @ thms)
          THEN' Simplifier.rewrite_goal_tac ctxt (#type_defs cogent_info)
          THEN' tac (Simplifier.addsimps (ctxt, cogent_info_funsimps cogent_info @ thms))
        )) 1) goal
        handle _ => raise ERROR ":("
  in
    case Seq.pull applytac of
      SOME (goal', _) =>
        (let
          val x = (Timing.result timing_leaf)
          val _ = if #cpu x >= TIMEOUT_WARN then (@{print tracing} "[leaf goal] took too long"; @{print tracing} (Thm.cprem_of goal 1); @{print tracing} x ; ()) else ()
        in
          goal'
        end)
    | NONE => raise ERROR ("(reduce_goal) failed to solve subgoal: " ^ @{make_string} (Thm.cprem_of goal 1))
  end

(* solve_misc_goal solved subgoals by recursively applying intro rules until we read a leaf, where
   we apply some tactic. It does not keep a record of how it solves things. *)
fun solve_misc_goal ctxt cogent_info goal (IntroStrat intros) =
  let
    val timer = Timing.start ()
    val x = (Timing.result timer)
    val _ = if #cpu x >= TIMEOUT_WARN then (@{print tracing} "[misc-goal 1 setup] took too long"; @{print tracing} x ; ()) else ()
    val timer = Timing.start ()
    val goal'_seq =
      (resolve_tac ctxt intros
      ORELSE' (Simplifier.rewrite_goal_tac ctxt (#type_defs cogent_info)
        THEN' resolve_tac ctxt intros)) 1 goal
    val goal' =
      case Seq.pull goal'_seq of
        SOME (goal', _) => goal'
      | NONE =>
        raise ERROR ("solve_misc_goal: failed to resolve goal " ^
                     @{make_string} goal ^
                     " with provided intro rules " ^
                     @{make_string} intros)
    val _ = if #cpu x >= TIMEOUT_WARN then (@{print tracing} "[misc-goal 1 solving] took too long"; @{print tracing} x ; ()) else ()
  in
    solve_misc_subgoals ctxt cogent_info goal'
  end
| solve_misc_goal ctxt cogent_info goal (ResolveNetStrat resolvenet) =
  let
    val timer = Timing.start ()
    val x = (Timing.result timer)
    val _ = if #cpu x >= TIMEOUT_WARN then (@{print tracing} "[misc-goal 2 setup] took too long"; @{print tracing} x ; ()) else ()
    val timer = Timing.start ()
    val goal'_seq = (resolve_from_net_tac ctxt resolvenet
                    ORELSE' (Simplifier.rewrite_goal_tac ctxt (#type_defs cogent_info)
                      THEN' resolve_from_net_tac ctxt resolvenet)) 1 goal
    val goal' = case Seq.pull goal'_seq of
      SOME (goal', _) => goal'
      | NONE =>
        raise ERROR ("solve_misc_goal: failed to resolve goal " ^
           @{make_string} goal ^
           " with provided net")
    val _ = if #cpu x >= TIMEOUT_WARN then (@{print tracing} "[misc-goal 2 solving] took too long"; @{print tracing} x ; ()) else ()
  in
    solve_misc_subgoals ctxt cogent_info goal'
  end
| solve_misc_goal ctxt cogent_info goal (LookupStrat name) =
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
    val timer = Timing.start ()
    val ctxt' = Simplifier.rewrite (Simplifier.addsimps (ctxt, cogent_info_funsimps cogent_info))
    val cleaned_goal =
      Conv.fconv_rule ctxt' goal'
    val x = (Timing.result timer)
    val _ = if #cpu x >= TIMEOUT_WARN then (@{print tracing} "[misc-goal cleanup] took too long"; @{print tracing} x ; ()) else ()
  in
    solve_misc_subgoals ctxt cogent_info cleaned_goal
  end
and solve_misc_subgoals ctxt cogent_fun_info goal =
  if Thm.no_prems goal
  then Goal.finish ctxt goal
  else
    let
      val subgoal = Thm.cprem_of goal 1
    in
      case subgoal |> Thm.term_of |> strip_trueprop |> goal_get_intros of
        SOME strat =>
          let
            val subgoal = subgoal |> Goal.init
            val timer = Timing.start ()
            val solved_subgoal = solve_misc_goal ctxt cogent_fun_info subgoal strat
            val x = (Timing.result timer)
            val _ = if #cpu x >= TIMEOUT_WARN_MISC_SUBG then (@{print tracing} "a misc-goal took too long"; @{print tracing} x ; ()) else ()
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
          reduce_goal ctxt cogent_fun_info goal subgoal
            |> solve_misc_subgoals ctxt cogent_fun_info
    end


(* solve_ttyping takes a cterm of a ttyping goal to be solved, then recursively solves by following
    the instructions from the hint tree. It keeps a record of the ttyping goals it has proven. *)
fun solve_ttyping ctxt cogent_info (Tree { value = Resolve intro, branches = hints }) goal : proof_status rtree =
  let
    val timer = Timing.start()
    val goalseq = (Simplifier.rewrite_goal_tac ctxt (#type_defs cogent_info)
                  THEN' resolve_tac ctxt [intro]) 1 goal
    val goal' =
      case Seq.pull goalseq of
        SOME (goal, _) => goal
      | NONE =>
        raise ERROR ("solve_misc_goal: failed to resolve goal " ^
                     @{make_string} goal ^
                     " with provided intro rules " ^
                     @{make_string} intro)
    val x = (Timing.result timer)
    val _ = if #cpu x >= TIMEOUT_WARN then (@{print tracing} "[solve_ttyping Tree] took too long"; @{print tracing} x ; ()) else ()
  in
     solve_subgoals ctxt cogent_info goal' hints []
  end
| solve_ttyping _ _ _ _ = error "solve got bad hints"
and solve_subgoals ctxt cogent_info goal (hint :: hints) solved_subgoals_rev : proof_status rtree = 
  let
    val timer = Timing.start ()
    val _ = if Thm.no_prems goal then (raise ERROR "tmp"; ()) else ()
    val ct_subgoal = Thm.major_prem_of goal |> Thm.cterm_of ctxt
    val subgoal = ct_subgoal |> Goal.init
    val x = (Timing.result timer)
    val _ = if #cpu x >= TIMEOUT_WARN then (@{print tracing} "[subgoal setup] took too long"; @{print tracing} x ; ()) else ()
  in
    (case hint of
      (Leaf _) =>
        (case ct_subgoal |> Thm.term_of |> strip_trueprop |> goal_get_intros of
          (SOME strat) =>
            let
              val thm_subgoal = solve_misc_goal ctxt cogent_info subgoal strat
              val solved_subgoal = Tree { value = ProofDone thm_subgoal, branches = [] }
            in
              solve_resolve_with_goal ctxt cogent_info goal solved_subgoal hints solved_subgoals_rev
            end
          | NONE =>
            let
              val goal' = reduce_goal ctxt cogent_info goal ct_subgoal
            in
              solve_subgoals ctxt cogent_info goal' hints solved_subgoals_rev
            end)
    | (Tree _) =>
      (let
        val solved_subgoal = solve_ttyping ctxt cogent_info hint subgoal
      in
        solve_resolve_with_goal ctxt cogent_info goal solved_subgoal hints solved_subgoals_rev
      end))
  end
| solve_subgoals ctxt _ goal [] solved_subgoals_rev =
  Tree { value = ProofDone (Goal.finish ctxt goal), branches = rev solved_subgoals_rev }
and solve_resolve_with_goal ctxt cogent_info goal solved_subgoal hints solved_subgoals_rev =
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
        solve_subgoals ctxt cogent_info goal' hints (solved_subgoal :: solved_subgoals_rev)
      end
    | _ => (* if the subgoal fails, the goal fails too *)
      Tree { value = ProofFailed { goal = goal, failed = solved_subgoal }, branches = rev solved_subgoals_rev })

fun get_typing_tree' ctxt cogent_info f script : thm rtree =
  let (* generate a simpset of all the definitions of the `f` function and typetree *)
      val defs = maps (Proof_Context.get_thms ctxt)
                    (map (prefix f) ["_def", "_type_def", "_typetree_def"]);
      val main_goal = (Syntax.read_term ctxt
         ("Trueprop (\<Xi>, fst " ^ f ^ "_type, (" ^ f ^ "_typetree, [Some (fst (snd " ^ f ^ "_type))])" ^
          "            T\<turnstile> " ^ f ^ " : snd (snd " ^ f ^ "_type))"))
        |> Thm.cterm_of ctxt
        |> Goal.init;
      val unfolded_goal = Simplifier.rewrite_goals_tac ctxt (@{thms HOL.eq_reflection[OF Product_Type.prod.sel(1)] HOL.eq_reflection[OF Product_Type.prod.sel(2)]} @ defs) main_goal
      val main_goal =
        case Seq.pull unfolded_goal of
          SOME (goal', _) => goal'
        | NONE => raise ERROR "todo: Seq.empty"
      val ctxt' = Simplifier.del_simp @{thm type_wellformed_pretty_def} ctxt
  in
    solve_ttyping ctxt' cogent_info script main_goal
    |> rtree_map (fn v =>
      case v of
        ProofDone tr => tr
      | _ => error ("get_typing_tree: failed for function " ^ f))
  end
*}

end