(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory TypeProofGen imports
  "../cogent/isa/ContextTrackingTyping"
  "../cogent/isa/ProofTrace"
  "../cogent/isa/TypeProofScript"
  "../cogent/isa/TypeProofTactic"
begin

ML_file "../l4v/tools/autocorres/mkterm_antiquote.ML"

(* Convert ttyping subproofs to standard typing subproofs. *)
lemma ttsplit_imp_split':
  "ttsplit k \<Gamma> xs \<Gamma>1 ys \<Gamma>2 \<Longrightarrow>
    k \<turnstile> snd \<Gamma> \<leadsto> drop (length xs) (snd \<Gamma>1) | drop (length ys) (snd \<Gamma>2)"
  by (fastforce dest: ttsplit_imp_split)

lemma ttsplit_inner_imp_split:
  assumes
    "ttsplit_inner K splits \<Gamma>b \<Gamma>1 \<Gamma>2"
    "list_all (\<lambda>s. s \<noteq> Some TSK_NS) splits"
  shows
    "K \<turnstile> snd (TyTrSplit splits xs T1 ys T2, \<Gamma>b) \<leadsto>
      drop (length xs) (snd (T1, xs @ \<Gamma>1)) | drop (length ys) (snd (T2, ys @ \<Gamma>2))"
  using assms ttsplit_imp_split
  by (fastforce simp add: ttsplit_def)

lemma ttsplit_bang_imp_split_bang':
  "ttsplit_bang k is \<Gamma> xs \<Gamma>1 ys \<Gamma>2 \<Longrightarrow>
    split_bang k is (snd \<Gamma>) (drop (length xs) (snd \<Gamma>1)) (drop (length ys) (snd \<Gamma>2))"
  by (fastforce dest: ttsplit_bang_imp_split_bang)

definition
  "duplicate_list xs = xs @ xs"

lemma replicate_numeral:
  "replicate (numeral (num.Bit0 n)) x = duplicate_list (replicate (numeral n) x)"                              
  "replicate (numeral (num.Bit1 n)) x = x # duplicate_list (replicate (numeral n) x)"
  "replicate (numeral num.One) x = [x]"
    apply (simp only: numeral_Bit0 replicate_add duplicate_list_def)
   apply (simp only: eval_nat_numeral(3) numeral_Bit0 replicate_Suc replicate_add duplicate_list_def)
  apply simp
  done

lemmas replicate_unfold = replicate_numeral replicate_Suc replicate_0 duplicate_list_def append.simps

declare [[ML_debugger = true]]

(* Generate type system lemma buckets *)
ML {*

(* identify judgements related to typing *)
fun is_typing t = head_of t |>
  (fn h => is_const "TypeTrackingSemantics.ttyping" h orelse
           is_const "TypeTrackingSemantics.ttsplit" h orelse
           is_const "TypeTrackingSemantics.ttsplit_bang" h orelse
           is_const "TypeTrackingSemantics.ttsplit_inner" h orelse
           is_const "Cogent.typing" h orelse
           is_const "Cogent.split" h orelse
           is_const "Cogent.kinding" h);

(* remove consecutive duplicates *)
fun uniq cmp (x::y::xs) = (case cmp (x,y) of EQUAL => uniq cmp (x::xs)
                                           | _ => x::uniq cmp (y::xs))
  | uniq _ xs = xs

fun get_typing_tree ctxt f proof : thm rtree list =
  let val abbrev_defs = Proof_Context.get_thms ctxt "abbreviated_type_defs"
                        handle ERROR _ => [];
      (* generate a simpset of all the definitions of the `f` function, type, and typetree *)
      val defs = maps (Proof_Context.get_thms ctxt)
                   (map (prefix f) ["_def", "_type_def", "_typetree_def"] @ ["replicate_unfold"])
                 @ abbrev_defs;
  in extract_subproofs
       (* The typing goal for `f` *)
       (Syntax.read_term ctxt
         ("Trueprop (\<Xi>, fst " ^ f ^ "_type, (" ^ f ^ "_typetree, [Some (fst (snd " ^ f ^ "_type))])" ^
          "            T\<turnstile> " ^ f ^ " : snd (snd " ^ f ^ "_type))")
        |> Thm.cterm_of ctxt)
       (let val hinted_tacs = map (fn (tag, t) => (SOME tag, t ctxt)) proof
            val all_tacs = (NONE, asm_full_simp_tac (ctxt addsimps defs) 1) :: hinted_tacs
          in all_tacs end)
       is_typing ctxt
     |> (fn r => case r of
            Right tr => tr
          | Left err => (@{print} err; error ("get_typing_tree failed for function " ^ f)))
  end


fun simplify_thm ctxt thm =
  Conv.fconv_rule (Simplifier.rewrite ctxt) thm

val strip_defeq = Thm.prop_of #> Logic.dest_equals #> snd


fun cleanup_typing_tree_thm ctxt thm = thm
    |> (fn t =>
        (t RS @{thm ttsplit_imp_split'}) handle THM _ =>
        (t RS @{thm ttsplit_inner_imp_split}) handle THM _ =>
        (t RS @{thm ttsplit_bang_imp_split_bang'}) handle THM _ =>
        (t RS @{thm ttyping_imp_typing(1)}) handle THM _ =>
        t
    |> simplify_thm ctxt)
  |> Thm.varifyT_global

fun get_final_typing_tree ctxt f proof =
  get_typing_tree ctxt f proof
  |> map (rtree_map (cleanup_typing_tree_thm ctxt))

(* covert a typing tree to a list of typing theorems *)
val typing_tree_to_bucket = rtree_flatten #> sort_distinct Thm.thm_ord

(*
fun get_typing_bucket ctxt f proof =
  get_typing_tree ctxt f proof
    |> map tree_flatten
    |> List.concat
    |> map (cleanup_typing_tree_thm ctxt)
    |> sort Thm.thm_ord
    |> uniq Thm.thm_ord
*)

type details = (thm list * thm rtree list * thm list)

open MkTermAntiquote

fun get_all_typing_details ctxt cogent_info name _ : details = let
(*
    val script_tree = (case parse_treesteps script of
        SOME tree => tree
      | NONE => raise ERROR ("failed to parse script tree"))
    val tacs = TTyping_Tactics.mk_ttsplit_tacs_final name
        @{term "[] :: kind env"} ctxt script_tree
    val tacs' = map (fn (tac, f) => (tac, fn ctxt => f ctxt 1)) tacs
*)
    val _ = (log_info ("[get_all_typing_details: " ^ name ^ "]"))
    val _ = (@{print tracing} ("[get_all_typing_details: " ^ name ^ "]"))
    val t1 = Timing.start () (* gen hints *)
    val expr = Proof_Context.get_thm ctxt (name ^ "_def")
      |> strip_defeq
    val hints = gen_script_ttyping expr
    val _ = (@{print tracing} ("[gen hints: " ^ name ^ "]"); @{print tracing} (Timing.result t1))
    val t2 = Timing.start () (* solve type-tree *)
    val orig_typing_tree = get_typing_tree' ctxt cogent_info name hints
    val _ = (log_info ("[solve type-tree: " ^ name ^ "]"))
    val _ = (@{print tracing} ("[solve type-tree: " ^ name ^ "]"); @{print tracing} (Timing.result t2))
    val typecorrect_thm = tree_value orig_typing_tree |> simplify ctxt |> Thm.varifyT_global
    val typing_tree : thm rtree = rtree_map (cleanup_typing_tree_thm ctxt) orig_typing_tree 
    val bucket : thm list = typing_tree_to_bucket typing_tree
  in ([typecorrect_thm], [typing_tree], bucket) end

fun get_all_typing_details_future ctxt absfuns name script
    = Future.fork (fn () => get_all_typing_details ctxt absfuns name script)

fun resolve_future_typecorrect ctxt details
    = resolve_tac ctxt (#1 (Future.join details : details)) 1
*}

end
