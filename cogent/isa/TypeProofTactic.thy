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

datatype Multiplier = Once | Many
datatype GoalStrategy = IntroStrat of Multiplier * thm list | LookupStrat of string | ResolveNetStrat of (int * thm) Net.net

(* nets *)
val subtyping_net = Tactic.build_net @{thms subtyping_refl subtyping.intros(1-5,7,9) subty_trecord' subty_tsum'}

fun introStratOnce ts = IntroStrat (Once,ts)
fun introStratMany ts = IntroStrat (Many,ts)

(* This is not any faster *)
(*
fun
  get_nth_last_arg (_ $ b) 0 = b
| get_nth_last_arg (a $ _) n = get_nth_last_arg a (n-1)
| get_nth_last_arg e _ = e

fun goal_get_intros t =
 let
  val f = Term.head_of t
  fun of_const f_nm = 
    (case f_nm of
    @{const_name ttyping_named} =>
      get_nth_last_arg t 2
      |> HOLogic.dest_string
      |> LookupStrat
      |> SOME
   | @{const_name "ttsplit"} => introStratMany @{thms ttsplitI ttsplit_inner_fun} |> SOME
   | @{const_name "ttsplit_inner"} => introStratOnce @{thms ttsplit_inner_fun} |> SOME
   | @{const_name "ttsplit_bang"} => introStratOnce @{thms ttsplit_bangI ttsplit_inner_fun} |> SOME
   | @{const_name "ttctxdup"} => introStratOnce @{thms ttctxdupI} |> SOME
   | @{const_name "tsk_split_comp"} => introStratOnce @{thms tsk_split_comp.intros} |> SOME
   | @{const_name "weakening"} =>
      (case get_nth_last_arg t 0 |> Term.head_of |> Term.dest_Const of
       (@{const_name singleton},_) =>
        introStratOnce @{thms singleton_weakening} |> SOME
      | _ =>
        introStratMany @{thms weakening_cons weakening_nil weakening_comp.intros} |> SOME)

   | @{const_name "weakening_comp"} => introStratOnce @{thms weakening_comp.intros} |> SOME
   | @{const_name "is_consumed"} =>
     introStratMany @{thms is_consumed_cons is_consumed_nil weakening_comp.intros} |> SOME
   | @{const_name "subtyping"} => subtyping_net |> ResolveNetStrat |> SOME
   | @{const_name "list_all2"} => introStratMany @{thms list_all2_nil list_all2_cons} |> SOME
   | _ => NONE)
 in
  (case f of
   Const (f_nm,_) => of_const f_nm
  | _ => NONE)
  end
*)

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
(* | goal_get_intros @{term_pat "type_wellformed_pretty _ _"}    = introStratOnce @{thms type_wellformed_pretty_intros} |> SOME *)
| goal_get_intros _ = NONE


datatype tac_types = Simp of thm list | Force of thm list | ForceWithRewrite of thm list * thm list | SimpOnly of thm list | UnknownTac

(* TODO the fact we need to specify all the possible misc goal patterns is a bit of a mess.
  Maybe just default to force with an expanded simpset when we don't know what to do?
  (the problem with this approach would be possible looping)
  ~ v.jackson / 2018.12.04 *)

(* This is not any faster *)
(*
fun goal_type_of_term t =
 let
  val f = Term.head_of t
  fun of_const @{const_name Cogent.kinding} = SOME (Force @{thms kinding_defs type_wellformed_pretty_def})
  (* "\<Xi> _ = _", "ttsplit_inner' _ _ _ = _" and "_ = _" *)
  | of_const @{const_name HOL.eq} = SOME (Force @{thms Cogent.empty_def type_wellformed_pretty_def kinding_defs})
  (* this case originally only applied for (_ \<noteq> _), so maybe check it's an equality underneath *)
  | of_const @{const_name HOL.Not} = SOME (Force @{thms Cogent.empty_def})
  | of_const @{const_name type_wellformed_pretty}  = SOME (Force @{thms type_wellformed_pretty_def})
  | of_const @{const_name Ex}                        = SOME (Force [])
  | of_const @{const_name All}                       = SOME (Force [])
  | of_const @{const_name conj}                       = SOME (Force [])
  | of_const @{const_name disj}                       = SOME (Force [])
  | of_const @{const_name less}                       = SOME (Force [])
  | of_const @{const_name Set.member}                       = SOME (Force [])
  | of_const @{const_name distinct}                  = SOME (Force [])
  | of_const @{const_name list_all}                = SOME (Force [])
  | of_const @{const_name list_all2}             = SOME (Force @{thms subtyping_simps})
  | of_const @{const_name upcast_valid}            = SOME (Force [])
  | of_const @{const_name is_consumed}             = SOME (Simp @{thms Cogent.is_consumed_def Cogent.empty_def Cogent.singleton_def})
  (* record_kind_subty - but that's an abbreviation *)
  | of_const @{const_name If}     = SOME (Force @{thms kinding_defs type_wellformed_pretty_def})
  (* variant_kind_subty *)
  | of_const @{const_name less_eq}      = SOME (Simp [])
  | of_const _                                         = NONE
 in
  case f of
   Const (n,_) => of_const n
   | _ => NONE
 end
*)


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
| goal_type_of_term _ @{term_pat "type_wellformed_pretty _ _"}  = SOME (Force @{thms type_wellformed_pretty_def})
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
| strip_trueprop _ = raise ERROR "strip_trueprop was passed something which isn't a Trueprop"

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
      | NONE => raise ERROR ("(solve_typeproof) unknown goal type for: " ^ @{make_string} (Thm.cprem_of goal num)))
    val (thms, tac) =
      case goal_type of
        Simp thms => (thms, Simplifier.simp_tac)
      | Force thms => (thms, fast_force_tac)
      | ForceWithRewrite (pre,thms) => (thms, fn ctxt' => Simplifier.rewrite_goal_tac ctxt pre THEN' fast_force_tac ctxt')
      | SimpOnly thms => (thms, fn _ => Simplifier.simp_tac (ctxt addsimps thms))
      | UnknownTac => raise ERROR ("Don't know what to do with: " ^ @{make_string} (Thm.cprem_of goal num))
    val tac_run = tac (Simplifier.addsimps (ctxt, cogent_info_funsimps cogent_info @ thms))
    fun tac_tryunroll thms' = Simplifier.rewrite_goal_tac ctxt thms' THEN' tac_run
    val applytac =
        (SOLVED' tac_run ORELSE' SOLVED' (tac_tryunroll (#type_defs cogent_info))) num goal
  in
    case Seq.pull applytac of
      SOME (goal', _) =>
        (let
          val x = (Timing.result timing_leaf)
          val _ = if #cpu x >= TIMEOUT_WARN then (@{print tracing} "[leaf goal] took too long"; @{print tracing} (Thm.cprem_of goal num); @{print tracing} x ; ()) else ()
        in
          goal'
        end)
    | NONE => raise ERROR ("(reduce_goal) failed to solve subgoal: " ^ @{make_string} (Thm.cprem_of goal num))
  end


fun solve_misc_goal_strat_exec ctxt cogent_info num goal  (SOME (IntroStrat (multiplier,intros))) =
  let
    val tac =
      case multiplier of
        Once => resolve_tac ctxt intros
      | Many => REPEAT_ALL_NEW (resolve_tac ctxt intros)
    val goal'_seq =
      (tac ORELSE' (Simplifier.rewrite_goal_tac ctxt (#type_defs cogent_info) THEN' tac)) num goal
    val goal' =
      case Seq.pull goal'_seq of
        SOME (goal', _) => goal'
      | NONE =>
        raise ERROR ("solve_misc_goal: failed to resolve goal " ^
                     @{make_string} goal ^
                     " with provided intro rules " ^
                     @{make_string} intros)
  in
    goal'
  end
| solve_misc_goal_strat_exec ctxt cogent_info num goal  (SOME (ResolveNetStrat resolvenet)) =
  let
    val goal'_seq = (resolve_from_net_tac ctxt resolvenet
                    ORELSE' (Simplifier.rewrite_goal_tac ctxt (#type_defs cogent_info)
                      THEN' resolve_from_net_tac ctxt resolvenet)) num goal
    val goal' = case Seq.pull goal'_seq of
      SOME (goal', _) => goal'
      | NONE =>
        raise ERROR ("solve_misc_goal: failed to resolve goal " ^
           @{make_string} goal ^
           " with provided net")
  in
    goal'
  end
| solve_misc_goal_strat_exec ctxt cogent_info num goal (SOME (LookupStrat name)) =
  let
    (* TODO this assumes things about generation *)
    val lookup_thm_name = (prefix "isa_" #> suffix "_typecorrect") name
    val lookup_thm = Proof_Context.get_thms ctxt lookup_thm_name
    val results = goal
      |> ((resolve_tac ctxt @{thms ttyping_named} num)
        THEN (resolve_tac ctxt lookup_thm num))
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
   then Goal.finish ctxt goal
   else (case solve_misc_goal' ctxt cogent_info 1 goal |> Seq.pull of
      SOME (goal,_) => go goal
    | NONE => raise ERROR ("solve_misc_goal: tactic failed: " ^ (@{make_string} goal)))
 in
  go goal
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
        raise ERROR ("solve_ttyping: failed to resolve goal " ^
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
    val t_subgoal = Thm.major_prem_of goal
    val ct_subgoal = t_subgoal |> Thm.cterm_of ctxt
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