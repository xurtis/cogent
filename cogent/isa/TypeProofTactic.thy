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

val TIMEOUT_WARN = Time.fromMilliseconds 1000000
val TIMEOUT_WARN_MISC_SUBG = Time.fromMilliseconds 1000000
val TIMEOUT_KILL = Time.fromMilliseconds 1000000 

fun rewrite_cterm ctxt =
       Simplifier.rewrite ctxt
    #> Thm.prop_of
    #> Logic.dest_equals
    #> snd

type cogent_info = { xidef : thm list, funs: thm list, absfuns: thm list, type_defs: thm list, type_defs_wellformed : (int * thm) Net.net }

val LOG_FILE = Path.basic "TypeProofTactic.log"
fun log_to_file strs = File.append LOG_FILE (strs ^"\n")
fun log_error str = log_to_file ("*** " ^ str)
fun log_info str  = log_to_file ("    " ^ str)
fun raise_error err =
  let
    val _   = log_error err
  in
     raise ERROR err
  end

fun init_type_defs_wellformed (ctxt : Proof.context) (type_defs : thm list) =
  let
    val t = Timing.start ()
    val all_defs_ctxt = ctxt addsimps type_defs
    fun prove_wf abbr_eq_def =
      case Thm.prop_of abbr_eq_def of
       @{term_pat "_ \<equiv> ?def"} =>
          let
            val wf_def_t      = @{mk_term "HOL.Trueprop (type_wellformed (length []) ?def)" def} def
            val wf_def_t      = Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt) type_defs [] wf_def_t
            val wf_def_thm    = Goal.prove ctxt [] [] wf_def_t (fn _ => fast_force_tac all_defs_ctxt 1)
          in
            wf_def_thm
          end
      | _ => 
       raise_error ("init_type_def_wellformed: " ^ @{make_string} abbr_eq_def)

    val all_wfs = Par_List.map prove_wf type_defs
    val simps   = (* simpset_of ((ctxt addsimps all_wfs delsimps @{thms type_wellformed.simps})) *)
                  Tactic.build_net all_wfs
    val _       = @{print tracing} "init_type_defs_wellformed: proved wellformedness:"
    val _       = @{print tracing} (Timing.result t)
  in
    simps
  end

fun cogent_info_funandtypesimps (cogent_info : cogent_info)
  = #funs cogent_info @ #absfuns cogent_info @ #type_defs cogent_info

fun cogent_info_funsimps (cogent_info : cogent_info)
  = #funs cogent_info @ #absfuns cogent_info

fun cogent_info_allsimps (cogent_info : cogent_info)
  = #xidef cogent_info @ #funs cogent_info @ #absfuns cogent_info @ #type_defs cogent_info

type tactic_context = { ctxt_main : Proof.context, ctxt_funsimps : Proof.context, tac_rewrite_type_defs : int -> tactic }

fun init_tactic_context
  (ctxt : Proof.context)
  (cogent_info : cogent_info)
    : tactic_context =
  let
    val ctxt_funsimps = ctxt addsimps (cogent_info_funsimps cogent_info)
    val tac_rewrite_type_defs = Simplifier.rewrite_goal_tac ctxt (#type_defs cogent_info)
  in
    { ctxt_main = ctxt
    , ctxt_funsimps = ctxt_funsimps
    , tac_rewrite_type_defs = tac_rewrite_type_defs }
  end


datatype Multiplier = Once | Many
datatype GoalStrategy = IntroStrat of Multiplier * thm list | LookupStrat of string | ResolveNetStrat of (int * thm) Net.net

(* nets *)
val subtyping_net = Tactic.build_net @{thms subtyping_refl subtyping.intros(1-5,7,9) subty_trecord' subty_tsum'}

fun introStratOnce ts = IntroStrat (Once,ts)
fun introStratMany ts = IntroStrat (Many,ts)

fun is_const_list @{term_pat "[]"} = true
| is_const_list @{term_pat "_ # ?bs"} = is_const_list bs
| is_const_list _ = false


fun goal_get_intros @{term_pat "ttyping_named _ _ _ ?name _ _"} =
   name
     |> HOLogic.dest_string
     |> LookupStrat
     |> SOME
| goal_get_intros @{term_pat "ttsplit _ _ _ _ _ _"}             = introStratMany @{thms ttsplitI ttsplit_inner_fun} |> SOME
| goal_get_intros @{term_pat "ttsplit_inner _ _ _ _ _"}         = introStratOnce @{thms ttsplit_inner_fun} |> SOME
| goal_get_intros @{term_pat "ttsplit_bang _ _ _ _ _ _ _"}      = introStratMany @{thms ttsplit_bangI ttsplit_inner_fun} |> SOME
| goal_get_intros @{term_pat "ttctxdup _ _ _ _ _"}              = introStratOnce @{thms ttctxdupI} |> SOME
| goal_get_intros @{term_pat "tsk_split_comp _ _ _ _ _"}        = introStratOnce @{thms tsk_split_comp.intros} |> SOME
| goal_get_intros @{term_pat "weakening _ _ (singleton _ _ _)"} = introStratOnce @{thms singleton_weakening} |> SOME
| goal_get_intros @{term_pat "weakening _ [] []"} = introStratOnce @{thms weakening_nil} |> SOME
| goal_get_intros @{term_pat "weakening _ (_ # ?b) (_ # ?c)"} =
  if is_const_list b andalso is_const_list c
  then introStratMany @{thms weakening_cons weakening_nil weakening_comp.intros} |> SOME
  else introStratOnce @{thms weakening_cons} |> SOME
| goal_get_intros @{term_pat "weakening_comp _ _ _"}            = introStratOnce @{thms weakening_comp.intros} |> SOME
| goal_get_intros @{term_pat "is_consumed _ ?a"} =
  if is_const_list a
  then introStratMany @{thms is_consumed_cons is_consumed_nil weakening_comp.intros} |> SOME
  else introStratOnce @{thms is_consumed_cons is_consumed_nil} |> SOME
| goal_get_intros @{term_pat "subtyping _ _ _"}                 = subtyping_net |> ResolveNetStrat |> SOME
| goal_get_intros @{term_pat "list_all2 _ [] []"}               = introStratOnce @{thms list_all2_nil} |> SOME
| goal_get_intros @{term_pat "list_all2 _ (_ # _) (_ # _)"}     = introStratMany @{thms list_all2_cons} |> SOME
| goal_get_intros _ = NONE


datatype tac_types = Simp of thm list | Force of thm list | ForceWithRewrite of thm list * thm list | SimpOnly of thm list | DoWellformed | UnknownTac

(* TODO the fact we need to specify all the possible misc goal patterns is a bit of a mess.
  Maybe just default to force with an expanded simpset when we don't know what to do?
  (the problem with this approach would be possible looping)
  ~ v.jackson / 2018.12.04 *)

fun goal_type_of_term (_ : cogent_info) @{term_pat "Cogent.kinding _ _ _"}      = SOME (Force @{thms kinding_defs type_wellformed_pretty_def})
| goal_type_of_term _ @{term_pat "ttsplit_inner' _ _ _ = _"} =
  SOME (SimpOnly @{thms type_wellformed_pretty_def kinding_defs})
  (* This rule is for "\<Xi> _ = _", but we can't match on that easily because the constant \<Xi> is not yet defined.
      We could do 'isSuffix "\<Xi>" nm' but that is surprisingly slow.
     Applying this rule is safe, because it's basically the same as "_ = _" *) 
| goal_type_of_term (cogent_info : cogent_info)
    (Const (@{const_name HOL.eq}, _) $ (Const (nm, _) $ _) $ _)
  = SOME (ForceWithRewrite (#xidef cogent_info, @{thms Cogent.empty_def}))
| goal_type_of_term _ @{term_pat "_ = _"}                       = SOME (Force @{thms Cogent.empty_def})
| goal_type_of_term _ @{term_pat "_ \<noteq> _"}                       = SOME (Force @{thms Cogent.empty_def})
| goal_type_of_term _ @{term_pat "type_wellformed_pretty _ _"}  = SOME DoWellformed
| goal_type_of_term _ @{term_pat "Ex _"}                        = SOME (Force [])
| goal_type_of_term _ @{term_pat "All _"}                       = SOME (Force [])
| goal_type_of_term _ @{term_pat "_ \<and> _"}                       = SOME (Force [])
| goal_type_of_term _ @{term_pat "_ \<or> _"}                       = SOME (Force [])
| goal_type_of_term _ @{term_pat "_ < _"}                       = SOME (Force [])
| goal_type_of_term _ @{term_pat "_ \<in> _"}                       = SOME (Force [])
| goal_type_of_term _ @{term_pat "distinct _"}                  = SOME (Force [])
| goal_type_of_term _ @{term_pat "list_all _ _"}                = SOME (Force [])
| goal_type_of_term _ @{term_pat "list_all2 _ _ _"}             = SOME (Force @{thms subtyping_simps})
(* | goal_type_of_term @{term_pat "subtyping _ _ _"}             = SOME (Force @{thms subtyping_simps}) *)
| goal_type_of_term _ @{term_pat "upcast_valid _ _"}            = SOME (Force [])
| goal_type_of_term _ @{term_pat "is_consumed _ _"}             = SOME (Simp @{thms Cogent.is_consumed_def Cogent.empty_def Cogent.singleton_def})
| goal_type_of_term _ @{term_pat "record_kind_subty _ _ _"}     = SOME (Force @{thms kinding_defs type_wellformed_pretty_def})
| goal_type_of_term _ @{term_pat "variant_kind_subty _ _"}      = SOME (Simp [])
| goal_type_of_term _ _                                         = NONE

fun strip_trueprop @{term_pat "HOL.Trueprop ?t"} = t
| strip_trueprop _ = raise_error "strip_trueprop was passed something which isn't a Trueprop"

datatype proof_status =
  ProofDone of thm
| ProofFailed of {
  goal : thm, (* the overall goal of the current proof *)
  failed : proof_status rtree (* the subgoal which failed *)
}
| ProofUnexpectedTerm of thm

fun reduce_goal ctxt cogent_info num goal =
  let
    val subgoal_t = List.nth (Thm.prems_of goal, num - 1)
    val timing_leaf = Timing.start ()
    val goal_type =
      (case subgoal_t |> strip_trueprop |> goal_type_of_term cogent_info of
        SOME goal_type => goal_type
      | NONE => raise_error ("(solve_typeproof) unknown goal type for: " ^ @{make_string} (Thm.cprem_of goal num)))
    val (thms, tac) =
      case goal_type of
        Simp thms => (thms, Simplifier.simp_tac)
      | Force thms => (thms, fast_force_tac)
      | ForceWithRewrite (pre,thms) => (thms, fn ctxt' => Simplifier.rewrite_goal_tac (#ctxt_main ctxt) pre THEN' fast_force_tac ctxt')
      | SimpOnly thms => (thms, Simplifier.simp_tac)
(*      | DoWellformed => ([], fn ctxt => fast_force_tac (ctxt addsimps @{thms type_wellformed_pretty_def})) *)
(*      | DoWellformed => ([], fn ctxt => fast_force_tac (put_simpset (#type_defs_wellformed cogent_info) ctxt)) *)

      | DoWellformed => ([], fn ctxt =>
                (Simplifier.rewrite_goal_tac ctxt @{thms type_wellformed_pretty_def}) THEN'
                (resolve_from_net_tac ctxt (#type_defs_wellformed cogent_info) ORELSE'
                (fast_force_tac ctxt)))
(*
      | DoWellformed => ([], fn ctxt =>
                (@{print tracing} "DoWellformed"; @{print tracing} (Thm.cprem_of goal num);
                Simplifier.rewrite_goal_tac ctxt @{thms type_wellformed_pretty_def}) THEN'
                (resolve_from_net_tac ctxt (#type_defs_wellformed cogent_info) ORELSE'
                (fn i => fn g => (@{print tracing} "Failed"; @{print tracing} (Thm.cprem_of g num); fast_force_tac (ctxt addsimps @{thms type_wellformed_pretty_def}) i g))))
*)
      | UnknownTac => raise_error ("Don't know what to do with: " ^ @{make_string} (Thm.cprem_of goal num))
    val tac_run = tac ((#ctxt_funsimps ctxt) addsimps thms)
    val tac_tryunroll = #tac_rewrite_type_defs ctxt THEN' tac_run
    val applytac =
	(Timeout.apply TIMEOUT_KILL
        	((SOLVED' tac_run ORELSE' SOLVED' tac_tryunroll) num) goal)
	handle _ => raise_error ("(reduce_goal) exceeded maximum time, killed")
  in
    case Seq.pull applytac of
      SOME (goal', _) =>
        (let
          val x = (Timing.result timing_leaf)
          val _ = if #cpu x >= TIMEOUT_WARN then (@{print tracing} "[leaf goal] took too long"; @{print tracing} (Thm.cprem_of goal num); @{print tracing} x ; ()) else ()
        in
          goal'
        end)
    | NONE => raise_error ("(reduce_goal) failed to solve subgoal: " ^ @{make_string} (Thm.cprem_of goal num))
  end


fun solve_misc_goal_strat_exec ctxt cogent_info num goal  (SOME (IntroStrat (multiplier,intros))) =
  let
    val tac =
      case multiplier of
        Once => resolve_tac (#ctxt_main ctxt) intros
      | Many => REPEAT_ALL_NEW (resolve_tac (#ctxt_main ctxt) intros)
    val goal'_seq =
      (tac ORELSE' (#tac_rewrite_type_defs ctxt THEN' tac)) num goal
    val goal' =
      case Seq.pull goal'_seq of
        SOME (goal', _) => goal'
      | NONE =>
        raise_error ("solve_misc_goal: failed to resolve goal " ^
                     @{make_string} goal ^
                     " with provided intro rules " ^
                     @{make_string} intros)
  in
    goal'
  end
| solve_misc_goal_strat_exec ctxt cogent_info num goal  (SOME (ResolveNetStrat resolvenet)) =
  let
    val goal'_seq = (resolve_from_net_tac (#ctxt_main ctxt) resolvenet
                    ORELSE' (#tac_rewrite_type_defs ctxt
                      THEN' resolve_from_net_tac (#ctxt_main ctxt) resolvenet)) num goal
    val goal' = case Seq.pull goal'_seq of
      SOME (goal', _) => goal'
      | NONE =>
        raise_error ("solve_misc_goal: failed to resolve goal " ^
           @{make_string} goal ^
           " with provided net")
  in
    goal'
  end
| solve_misc_goal_strat_exec ctxt cogent_info num goal (SOME (LookupStrat name)) =
  let
    (* TODO this assumes things about generation *)
    val lookup_thm_name = (prefix "isa_" #> suffix "_typecorrect") name
    val lookup_thm = Proof_Context.get_thms (#ctxt_main ctxt) lookup_thm_name
    val results = goal
      |> ((resolve_tac (#ctxt_main ctxt) @{thms ttyping_named} num)
        THEN (resolve_tac (#ctxt_main ctxt) lookup_thm num))
    val goal' = (case Seq.pull results of
        SOME (goal, _) => goal
      | NONE => raise_error ("solve_typing_goal: failed to apply named thm " ^ (@{make_string} goal)))
    val timer = Timing.start ()
    val ctxt' = Simplifier.rewrite (#ctxt_funsimps ctxt)
    val cleaned_goal =
      Conv.fconv_rule ctxt' goal'
    val x = (Timing.result timer)
    val _ = if #cpu x >= TIMEOUT_WARN then (@{print tracing} "[misc-goal cleanup] took too long"; @{print tracing} x ; ()) else ()
  in
    cleaned_goal
  end
| solve_misc_goal_strat_exec ctxt cogent_info num goal NONE =
   reduce_goal ctxt cogent_info num goal


fun solve_misc_goal' ctxt cogent_info num goal =
  let
    val prem0 = Thm.cprem_of goal num
    val subgoal_t = List.nth (Thm.prems_of goal, num - 1)
    val strat = subgoal_t |> strip_trueprop |> goal_get_intros
    val timer = Timing.start ()
    val goal = solve_misc_goal_strat_exec ctxt cogent_info num goal strat
    val x = (Timing.result timer)
    val _ = if #cpu x >= TIMEOUT_WARN_MISC_SUBG then (@{print tracing} "a misc-goal took too long"; @{print tracing} prem0; @{print tracing} x ; ()) else ()
  in
    Seq.single goal
  end

(* like REPEAT_ALL_NEW, except go *forwards* in subgoals instead of backwards *)
fun solve_misc_goal ctxt cogent_info goal =
 let
  fun go goal =
   if Thm.nprems_of goal = 0
   then Goal.finish (#ctxt_main ctxt) goal
   else (case solve_misc_goal' ctxt cogent_info 1 goal |> Seq.pull of
      SOME (goal,_) => go goal
    | NONE => raise_error ("solve_misc_goal: tactic failed: " ^ (@{make_string} goal)))
 in
  go goal
 end


(* solve_ttyping takes a cterm of a ttyping goal to be solved, then recursively solves by following
    the instructions from the hint tree. It keeps a record of the ttyping goals it has proven. *)
fun solve_ttyping ctxt cogent_info (Tree { value = Resolve intro, branches = hints }) goal : proof_status rtree =
  let
    val timer = Timing.start()
    val goalseq = (#tac_rewrite_type_defs ctxt
                  THEN' resolve_tac (#ctxt_main ctxt) [intro]) 1 goal
    val goal' =
      case Seq.pull goalseq of
        SOME (goal, _) => goal
      | NONE =>
        raise_error ("solve_ttyping: failed to resolve goal " ^
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
    val _ = if Thm.no_prems goal then (raise_error "solve_subgoals: no goals left, but expected goal"; ()) else ()
    val t_subgoal = Thm.major_prem_of goal
    val ct_subgoal = t_subgoal |> Thm.cterm_of (#ctxt_main ctxt)
    val subgoal = ct_subgoal |> Goal.init
    val x = (Timing.result timer)
    val _ = if #cpu x >= TIMEOUT_WARN then (@{print tracing} "[subgoal setup] took too long"; @{print tracing} x ; ()) else ()
  in
    (case hint of
      (Leaf _) =>
        (case ct_subgoal |> Thm.term_of |> strip_trueprop |> goal_get_intros of
          (SOME _) =>
            let
              val thm_subgoal = solve_misc_goal ctxt cogent_info subgoal
              val solved_subgoal = Tree { value = ProofDone thm_subgoal, branches = [] }
            in
              solve_resolve_with_goal ctxt cogent_info goal solved_subgoal hints solved_subgoals_rev
            end
          | NONE =>
            let
              val goal' = reduce_goal ctxt cogent_info 1 goal
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
  Tree { value = ProofDone (Goal.finish (#ctxt_main ctxt) goal), branches = rev solved_subgoals_rev }
and solve_resolve_with_goal ctxt cogent_info goal solved_subgoal hints solved_subgoals_rev =
  (* we solved the subgoal, resolve it with our goal to make the goal smaller *)
  (case tree_value solved_subgoal of
    ProofDone thm_subgoal =>
      let
        val goal' =
          case Seq.pull (resolve_tac (#ctxt_main ctxt) [thm_subgoal] 1 goal) of
            SOME (thm_soln, _) => thm_soln
          | NONE => (* this shouldn't happen! *)
            raise_error ("failed to resolve subgoal (" ^ @{make_string} goal ^ ") with solved subgoal: " ^ (@{make_string} thm_subgoal))
      in
        solve_subgoals ctxt cogent_info goal' hints (solved_subgoal :: solved_subgoals_rev)
      end
    | _ => (* if the subgoal fails, the goal fails too *)
      Tree { value = ProofFailed { goal = goal, failed = solved_subgoal }, branches = rev solved_subgoals_rev })

fun get_typing_tree' ctxt cogent_info f script : thm rtree =
  (let (* generate a simpset of all the definitions of the `f` function and typetree *)
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
        | NONE => raise_error "todo: Seq.empty"
      val ctxt' = Simplifier.del_simp @{thm type_wellformed_pretty_def} ctxt
      val tac_ctxt = init_tactic_context ctxt' cogent_info
  in
    solve_ttyping tac_ctxt cogent_info script main_goal
    |> rtree_map (fn v =>
      case v of
        ProofDone tr => tr
      | _ => error ("get_typing_tree: failed for function " ^ f))
  end)
    handle ERROR err => raise_error ("get_typing_tree': caught error: " ^ err)
*}

end
