(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory ContextTrackingTyping
  imports Cogent
begin

text \<open>ContextTrackingTyping are a rewrite of the Cogent typing rules to handle splitting
  deterministically.

  The Cogent verification process starts with the compiler handing us several expressions, and
  their typings. Our goal is to prove these typings are correct. The typing rules in `Cogent.thy`,
  while an adequate specification of a correct typing, do not give us a very good way to
  deterministically prove such a typing. The issue is that you can't tell how the contexts should
  split when doing backwards reasoning; moreover, the number of possible splittings is exponential.

  The introduction rules in this file are ordered very carefully to avoid unification looping, and
  to ensure we evaluate sub-goals that actually have enough information to proceed.
\<close>

datatype type_split_op =
  TSK_R    \<comment>\<open> Split Right \<close>
  | TSK_L  \<comment>\<open> Split Left  \<close>
  | TSK_S  \<comment>\<open> Split Share \<close>
  | TSK_NS \<comment>\<open> Split Bang  \<close>

(* An explicit typing tree
*)
datatype typing_tree =
  \<comment> \<open> Split the context. Firstly, how to split it.
      Then additional on the left, and instructions for that sub-tree.
      Then additional on the right, and instructions for that sub-tree. \<close>
  TyTrSplit "type_split_op option list" ctx typing_tree ctx typing_tree
  \<comment> \<open> Functions are special, in that we don't let them capture anything in the context,
       which means we essentially consume everything, and then set up a new context \<close>
  | TyTrFun name
  | TyTrTriv ctx typing_tree ctx typing_tree
  | TyTrLeaf

type_synonym tree_ctx = "typing_tree * ctx"

subsection {* Split from Split-ops *}

fun apply_tsk :: "type_split_op option \<Rightarrow> type option \<Rightarrow> type option \<times> type option" where
    "apply_tsk (Some TSK_R)  t = (None, t)"
  | "apply_tsk (Some TSK_L)  t = (t, None)"
  | "apply_tsk (Some TSK_S)  t = (t, t)"
  | "apply_tsk (Some TSK_NS) t = (map_option bang t, t)"
  | "apply_tsk None None       = (None, None)"

fun follow_typing_tree :: "tree_ctx \<Rightarrow> tree_ctx \<times> tree_ctx" where
  "follow_typing_tree (TyTrSplit sps xs T1 ys T2, \<Gamma>) =
    (let split\<Gamma> = (List.map2 apply_tsk sps \<Gamma>)
      in ((T1, xs @ map fst split\<Gamma>), (T2, ys @ map snd split\<Gamma>)))"
| "follow_typing_tree (TyTrTriv xs T1 ys T2, \<Gamma>) =
    ((T1, xs @ \<Gamma>), (T2, ys @ \<Gamma>))"


section {* split with explicit choice of action *}

inductive tsk_split_comp :: "kind env \<Rightarrow> type_split_op option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool"
          ("_ T\<turnstile> _ , _ \<leadsto> _ \<parallel> _" [30,0,0,20] 60) where
  none  : "K T\<turnstile> None , None \<leadsto> None \<parallel> None"
| left  : "\<lbrakk> K \<turnstile> t wellformed \<rbrakk> \<Longrightarrow> K T\<turnstile> Some TSK_L , Some t \<leadsto> Some t \<parallel> None"
| right : "\<lbrakk> K \<turnstile> t wellformed \<rbrakk> \<Longrightarrow> K T\<turnstile> Some TSK_R , Some t \<leadsto> None   \<parallel> Some t"
| share : "\<lbrakk> K \<turnstile> t :\<kappa> {S}     \<rbrakk> \<Longrightarrow> K T\<turnstile> Some TSK_S , Some t \<leadsto> Some t \<parallel> Some t"
| bang  : "\<lbrakk> K \<turnstile> t wellformed ; t' = bang t \<rbrakk> \<Longrightarrow> K T\<turnstile> Some TSK_NS , Some t \<leadsto> Some t' \<parallel> Some t"
declare tsk_split_comp.intros[intro!]

subsection {* Split-ops from Splits *}

fun split_tsk :: "type option \<Rightarrow> type option \<Rightarrow> type_split_op option" where
    "split_tsk (Some _) (Some _) = Some TSK_S"
  | "split_tsk None (Some _) = Some TSK_R"
  | "split_tsk (Some _) None = Some TSK_L"
  | "split_tsk None None = None"

fun split_bang_tsk :: "bool \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type_split_op option" where
    "split_bang_tsk True (Some _) (Some _) = Some TSK_NS"
  | "split_bang_tsk False t1 t2 = split_tsk t1 t2"

lemma split_tsk_never_ns: "split_tsk t1 t2 \<noteq> Some TSK_NS"
  using split_tsk.elims by auto

lemma split_tsk_ns_imp_b: "split_bang_tsk b t1 t2 = Some TSK_NS \<Longrightarrow> b"
  by (metis (full_types) split_bang_tsk.simps(2) split_tsk_never_ns)

lemma split_comp_by_split_tsk:
  assumes
    "K \<turnstile> x \<leadsto> x1 \<parallel> x2"
  shows
    "K T\<turnstile> split_tsk x1 x2, x \<leadsto> x1 \<parallel> x2"
  using assms
  by (force elim!: split_comp.cases simp: kinding_def)

lemma tsk_split_comp_not_ns_imp_split_comp:
  assumes
    "K T\<turnstile> s, x \<leadsto> x1 \<parallel> x2"
    "s \<noteq> Some TSK_NS"
  shows "K \<turnstile> x \<leadsto> x1 \<parallel> x2"
  using assms
  by (auto elim!: tsk_split_comp.cases simp: kinding_def intro: split_comp.intros)

lemma split_comp_imp_tsk_split_comp_not_ns:
  assumes
    "K , b \<turnstile> x \<leadsto>b x1 \<parallel> x2"
  shows
    "K T\<turnstile> split_bang_tsk b x1 x2, x \<leadsto> x1 \<parallel> x2"
  using assms
  by (fastforce elim!: split_bang_comp.cases split_comp.cases simp add: supersumption)

lemma split_bang_comp_by_split_bang_tsk:
  assumes
    "i < length \<Gamma>"
    "K , i \<in> is \<turnstile> \<Gamma> ! i \<leadsto>b \<Gamma>1 ! i \<parallel> \<Gamma>2 ! i"
  shows
    "(split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i) = None) = (\<Gamma> ! i = None)"
    "split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i) = Some TSK_L \<Longrightarrow> (\<exists>t. \<Gamma> ! i = Some t \<and> type_wellformed (length K) t)"
    "split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i) = Some TSK_R \<Longrightarrow> (\<exists>t. \<Gamma> ! i = Some t \<and> type_wellformed (length K) t)"
    "split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i) = Some TSK_NS \<Longrightarrow> (\<exists>t. \<Gamma> ! i = Some t \<and> type_wellformed (length K) t)"
    "split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i) = Some TSK_S \<Longrightarrow> (\<exists>t. \<Gamma> ! i = Some t \<and> K \<turnstile> t :\<kappa> {S})"
  using assms
  by (auto elim!: split_bang_comp.cases split_comp.cases simp: kinding_def)

lemma split_bang_comp_with_true_forces_ns:
  assumes
    "i < length \<Gamma>"
    "K , True \<turnstile> \<Gamma> ! i \<leadsto>b \<Gamma>1 ! i \<parallel> \<Gamma>2 ! i"
  shows
    "split_bang_tsk True (\<Gamma>1 ! i) (\<Gamma>2 ! i) = Some TSK_NS"
  using assms
  by (auto elim!: split_bang_comp.cases split_comp.cases simp: kinding_def)

lemma split_bang_imp_\<Gamma>1_\<Gamma>2_are:
  assumes
    "K , is \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2"
  shows
    "\<Gamma>1 =
    List.map2 (\<lambda>x y. if x = Some TSK_L \<or> x = Some TSK_S then y else if x = Some TSK_NS then map_option bang y else None)
     (map (\<lambda>i. split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i)) [0..<length \<Gamma>]) \<Gamma>"
    "\<Gamma>2 =
    List.map2 (\<lambda>x y. if x = Some TSK_R \<or> x = Some TSK_S \<or> x = Some TSK_NS then y else None)
     (map (\<lambda>i. split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i)) [0..<length \<Gamma>]) \<Gamma>"
  using assms
proof (induct rule: split_bang.inducts)
  case (split_bang_cons K "is" xs as bs x a b)
  let ?orig = "(map (\<lambda>i. split_bang_tsk (i \<in> is) ((a # as) ! i) ((b # bs) ! i)) [0..<length (x # xs)])"
  let ?new = "split_bang_tsk (0 \<in> is) a b # (map (\<lambda>i. split_bang_tsk (i \<in> pred ` Set.remove 0 is) (as ! i) (bs ! i)) [0..<length xs])"
  have f1: "?orig = ?new"
    by (clarsimp simp del: upt_Suc simp add: map_upt_Suc Suc_mem_image_pred_remove)
  
  show "a # as =
       List.map2 (\<lambda>x y. if x = Some TSK_L \<or> x = Some TSK_S then y else if x = Some TSK_NS then map_option bang y else None)
        (map (\<lambda>i. split_bang_tsk (i \<in> is) ((a # as) ! i) ((b # bs) ! i)) [0..<length (x # xs)]) (x # xs)"
    using split_bang_cons f1
    by (fastforce elim!: split_bang_comp.cases split_comp.cases)
  show "b # bs =
       List.map2 (\<lambda>x y. if x = Some TSK_R \<or> x = Some TSK_S \<or> x = Some TSK_NS then y else None)
        (map (\<lambda>i. split_bang_tsk (i \<in> is) ((a # as) ! i) ((b # bs) ! i)) [0..<length (x # xs)]) (x # xs)"
    using split_bang_cons f1
    by (fastforce elim!: split_bang_comp.cases split_comp.cases)
qed simp+


section {* ttsplit *}

definition ttsplit_inner :: "kind env \<Rightarrow> type_split_op option list \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool"
where
  "ttsplit_inner K \<equiv> list_all4 (tsk_split_comp K)"


lemmas ttsplit_inner_induct = 
  list_all4_induct[where P="tsk_split_comp K"  for K, simplified ttsplit_inner_def[symmetric],
    consumes 1, case_names Nil Cons, induct set: list_all4]

lemmas ttsplit_inner_iff =
  list_all4_iff[where P="tsk_split_comp K"  for K, simplified ttsplit_inner_def[symmetric]]

lemmas ttsplit_inner_conv_all_nth =
  list_all4_conv_all_nth[where P="tsk_split_comp K"  for K, simplified ttsplit_inner_def[symmetric]]

lemmas ttsplit_inner_Cons =
  list_all4_Cons[where P="tsk_split_comp K"  for K, simplified ttsplit_inner_def[symmetric]]
lemmas ttsplit_inner_Cons1 =
  list_all4_Cons1[where P="tsk_split_comp K"  for K, simplified ttsplit_inner_def[symmetric]]
lemmas ttsplit_inner_Cons2 =
  list_all4_Cons2[where P="tsk_split_comp K"  for K, simplified ttsplit_inner_def[symmetric]]
lemmas ttsplit_inner_Cons3 =
  list_all4_Cons3[where P="tsk_split_comp K"  for K, simplified ttsplit_inner_def[symmetric]]
lemmas ttsplit_inner_Cons4 =
  list_all4_Cons4[where P="tsk_split_comp K"  for K, simplified ttsplit_inner_def[symmetric]]

lemma ttsplit_inner_lengthD:
  assumes "ttsplit_inner K sps \<Gamma>a \<Gamma>1a \<Gamma>2a"
  shows  "length sps = length \<Gamma>a \<and> length \<Gamma>a = length \<Gamma>1a \<and> length \<Gamma>1a = length \<Gamma>2a"
  using assms ttsplit_inner_conv_all_nth by auto

definition ttsplit :: "kind env \<Rightarrow> tree_ctx \<Rightarrow>
        ctx \<Rightarrow> tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> bool"
  where
  "ttsplit K p xs p1 ys p2 =
    (let (Ta, \<Gamma>a) = p
      ; (T1, \<Gamma>1) = p1
      ; (T2, \<Gamma>2) = p2
    in \<exists>sps.
        Ta = TyTrSplit sps xs T1 ys T2 \<and>
        (list_all (\<lambda>s. s \<noteq> Some TSK_NS) sps) \<and>
        (\<exists>\<Gamma>1a \<Gamma>2a.
          ttsplit_inner K sps \<Gamma>a \<Gamma>1a \<Gamma>2a \<and>
          (\<Gamma>1 = xs @ \<Gamma>1a) \<and>
          (\<Gamma>2 = ys @ \<Gamma>2a))
)"


definition ttsplit_triv :: "tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> bool"
  where
    "ttsplit_triv p xs p1 ys p2 =
      (let (T, \<Gamma>) = p
        ; (T1, \<Gamma>1) = p1
        ; (T2, \<Gamma>2) = p2
      in (T = TyTrTriv xs T1 ys T2) \<and> (\<Gamma>1 = xs @ \<Gamma>) \<and> (\<Gamma>2 = ys @ \<Gamma>))"

definition ttsplit_bang :: "kind env \<Rightarrow> nat set \<Rightarrow> tree_ctx
        \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> ctx \<Rightarrow> tree_ctx \<Rightarrow> bool"
  where
  "ttsplit_bang K is p xs p1 ys p2 =
    (let (Ta, \<Gamma>a) = p
      ; (T1, \<Gamma>1) = p1
      ; (T2, \<Gamma>2) = p2
    in \<exists>sps.
        Ta = TyTrSplit sps xs T1 ys T2 \<and>
        (\<forall>i < length \<Gamma>a. (i \<in> is) = (sps ! i = Some TSK_NS)) \<and>
        (\<exists>\<Gamma>1a \<Gamma>2a.
          ttsplit_inner K sps \<Gamma>a \<Gamma>1a \<Gamma>2a \<and>
          (\<Gamma>1 = xs @ \<Gamma>1a) \<and>
          (\<Gamma>2 = ys @ \<Gamma>2a))
      )"

subsection {* ttsplit lemmas *}

subsubsection {* ttsplit *}

lemma ttsplitI:
  assumes
    "ttsplit_inner K sps \<Gamma>a \<Gamma>1a \<Gamma>2a"
    "xsa = xs"
    "ysa = ys"
    "xs' = xs @ \<Gamma>1a"
    "ys' = ys @ \<Gamma>2a"
    "list_all (\<lambda>s. s \<noteq> Some TSK_NS) sps"
  shows "ttsplit K (TyTrSplit sps xs T1 ys T2, \<Gamma>a) xsa (T1, xs') ysa (T2, ys')"
  using assms by (simp add: ttsplit_def)

lemma ttsplit_imp_split:
  assumes "ttsplit K \<Gamma> xs \<Gamma>1 ys \<Gamma>2"
  shows "\<exists>\<Gamma>1a \<Gamma>2a. (K \<turnstile> (snd \<Gamma>) \<leadsto> \<Gamma>1a | \<Gamma>2a) \<and> snd \<Gamma>1 = xs @ \<Gamma>1a \<and> snd \<Gamma>2 = ys @ \<Gamma>2a"
  using assms
  by (fastforce
      elim!: tsk_split_comp.cases
      intro: split_comp.intros tsk_split_comp_not_ns_imp_split_comp
      simp add: ttsplit_def ttsplit_inner_conv_all_nth split_conv_all_nth list_all_length)

lemma split_imp_ttsplit:
  assumes
    "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    "sps = map (\<lambda>i. split_tsk (\<Gamma>1 ! i) (\<Gamma>2 ! i)) [0 ..< length \<Gamma>]"
    "\<Gamma>1' = xs @ \<Gamma>1"
    "\<Gamma>2' = ys @ \<Gamma>2"
  shows "ttsplit K (TyTrSplit sps xs tt ys tt2, \<Gamma>) xs (tt, \<Gamma>1') ys (tt2, \<Gamma>2')"
  using assms
  unfolding ttsplit_def
  by (clarsimp simp add: ttsplit_inner_conv_all_nth split_conv_all_nth list_all_length
      split_comp_by_split_tsk split_tsk_never_ns)

lemma split_imp_ttsplitD:
  assumes
    "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  shows "ttsplit K
    (TyTrSplit
      (map (\<lambda>i. split_tsk (\<Gamma>1 ! i) (\<Gamma>2 ! i)) [0 ..< length \<Gamma>])
      xs tt ys tt2, \<Gamma>)
      xs (tt, xs @ \<Gamma>1)
      ys (tt2, ys @ \<Gamma>2)"
  using assms split_imp_ttsplit
  by simp

subsubsection {* ttsplit_triv *}

lemma ttsplit_trivI:
  assumes
    "\<Gamma>1b = (\<Gamma>1a, xs @ \<Gamma>b)"
    "\<Gamma>2b = (\<Gamma>2a, ys @ \<Gamma>b)"
  shows "ttsplit_triv (TyTrTriv xs \<Gamma>1a ys \<Gamma>2a, \<Gamma>b) xs \<Gamma>1b ys \<Gamma>2b"
  using assms by (simp add: ttsplit_triv_def)

subsubsection {* ttsplit_bang *}

lemma ttsplit_bangI:
  assumes
    "xs' = xs @ \<Gamma>1a"
    "ys' = ys @ \<Gamma>2a"
    "is = set (map fst (filter (\<lambda>(i, v). v = Some TSK_NS) (enumerate 0 sps)))"
    "ttsplit_inner K sps \<Gamma>b \<Gamma>1a \<Gamma>2a"
  shows "ttsplit_bang K is (TyTrSplit sps xs T1 ys T2, \<Gamma>b) xs (T1, xs') ys (T2, ys')"
  using assms
  by (force dest: ttsplit_inner_lengthD simp add: ttsplit_bang_def image_def in_set_enumerate_eq)

lemma ttsplit_bang_imp_split_bang:
  assumes "ttsplit_bang K is \<Gamma> xs \<Gamma>1 ys \<Gamma>2"
  shows "\<exists>\<Gamma>1a \<Gamma>2a. (K, is \<turnstile> (snd \<Gamma>) \<leadsto>b \<Gamma>1a | \<Gamma>2a) \<and> snd \<Gamma>1 = xs @ \<Gamma>1a \<and> snd \<Gamma>2 = ys @ \<Gamma>2a"
  using assms
proof (clarsimp simp: ttsplit_bang_def)
  fix \<Gamma>a T1 T2  sps \<Gamma>1a \<Gamma>2a
  assume
    "ttsplit_inner K sps \<Gamma>a \<Gamma>1a \<Gamma>2a"
    "\<Gamma> = (TyTrSplit sps xs T1 ys T2, \<Gamma>a)"
    "\<Gamma>1 = (T1, xs @ \<Gamma>1a)"
    "\<Gamma>2 = (T2, ys @ \<Gamma>2a)"
    "\<forall>i<length \<Gamma>a. (i \<in> is) = (sps ! i = Some TSK_NS)"
  then show "K , is \<turnstile> \<Gamma>a \<leadsto>b \<Gamma>1a | \<Gamma>2a"
  proof (induct arbitrary: "is" \<Gamma> \<Gamma>1 \<Gamma>2 rule: ttsplit_inner_induct)
    case (Cons s sps' x \<Gamma>' x1 \<Gamma>1' x2 \<Gamma>2')
    moreover then have "K , pred ` Set.remove 0 is \<turnstile> \<Gamma>' \<leadsto>b \<Gamma>1' | \<Gamma>2'"
      by (force simp add: Suc_mem_image_pred_remove)
    ultimately show ?case
      by (fastforce intro: split_bang.intros elim!: tsk_split_comp.cases
          simp add: split_bang_comp.simps split_comp.simps kinding_def)
  qed (simp add: split_bang.intros)
qed

lemma split_bang_imp_ttsplit_bang:
  assumes
    "K , is \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2"
    "sps = map (\<lambda>i. split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i)) [0 ..< length \<Gamma>]"
    "\<Gamma>1' = xs @ \<Gamma>1"
    "\<Gamma>2' = ys @ \<Gamma>2"
  shows "ttsplit_bang K is (TyTrSplit sps xs tt ys tt2, \<Gamma>) xs (tt, \<Gamma>1') ys (tt2, \<Gamma>2')"
  using assms
  unfolding ttsplit_bang_def
  by (auto dest: split_tsk_ns_imp_b simp add: ttsplit_inner_conv_all_nth split_bang_nth
      split_comp_imp_tsk_split_comp_not_ns split_bang_comp_with_true_forces_ns)

lemma split_bang_imp_ttsplit:
  assumes "split_bang K is \<Gamma> \<Gamma>1 \<Gamma>2"
  shows "\<exists>sps. \<forall>xs ys \<Gamma>1' \<Gamma>2'.
      (\<Gamma>1' = xs @ \<Gamma>1 
      \<longrightarrow> \<Gamma>2' = ys @ \<Gamma>2
      \<longrightarrow> ttsplit_bang K is (TyTrSplit sps xs tt ys tt2, \<Gamma>) xs (tt, \<Gamma>1') ys (tt2, \<Gamma>2'))"
  using assms
  by (force intro!: split_bang_imp_ttsplit_bang)

subsubsection {* ttsplit_inner *}

lemma ttsplit_innerI:
  "\<lbrakk> K T\<turnstile> s , x \<leadsto> a \<parallel> b ; ttsplit_inner K sps \<Gamma>a \<Gamma>1a \<Gamma>2a \<rbrakk>
    \<Longrightarrow> ttsplit_inner K (s # sps) (x # \<Gamma>a) (a # \<Gamma>1a) (b # \<Gamma>2a)"
  "ttsplit_inner K [] [] [] []"
  by (clarsimp simp add: ttsplit_inner_Cons ttsplit_inner_def)+

lemma ttsplit_inner_to_map_eqD:
  assumes "ttsplit_inner K sps \<Gamma>a \<Gamma>1a \<Gamma>2a"
  shows
    "length \<Gamma>1a = length \<Gamma>2a \<and> zip \<Gamma>1a \<Gamma>2a = List.map2 apply_tsk sps \<Gamma>a"
  using assms
  by (fastforce elim: tsk_split_comp.cases simp add: list_eq_iff_nth_eq ttsplit_inner_conv_all_nth)+

subsubsection {* general lemmas *}

lemma split_follow_typing_tree:
  "ttsplit K \<Gamma> xs' \<Gamma>1 ys' \<Gamma>2 \<Longrightarrow> (\<Gamma>1, \<Gamma>2) = follow_typing_tree \<Gamma>"
  "ttsplit_triv \<Gamma> xs' \<Gamma>1 ys' \<Gamma>2 \<Longrightarrow> (\<Gamma>1, \<Gamma>2) = follow_typing_tree \<Gamma>"
  "ttsplit_bang K is \<Gamma> xs' \<Gamma>1 ys' \<Gamma>2 \<Longrightarrow> (\<Gamma>1, \<Gamma>2) = follow_typing_tree \<Gamma>"
  by (force dest: ttsplit_inner_to_map_eqD simp add: ttsplit_def ttsplit_triv_def ttsplit_bang_def zip_eq_conv)+

section {* TTyping *}

inductive ttyping :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> tree_ctx \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool"
          ("_, _, _ T\<turnstile> _ : _" [30,0,0,0,20] 60)
      and ttyping_all :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> tree_ctx \<Rightarrow> 'f expr list \<Rightarrow> type list \<Rightarrow> bool"
          ("_, _, _ T\<turnstile>* _ : _" [30,0,0,0,20] 60)
      and ttyping_named :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> tree_ctx \<Rightarrow> name \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool"
          ("_, _, _ [ _ ]T\<turnstile> _ : _" [30,0,0,0,20] 60) \<comment> \<open> used to find typing rules we've already solved \<close>
      where

  ttyping_var    : "\<lbrakk> K \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i t
                    ; i < length \<Gamma>
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, (TyTrLeaf, \<Gamma>) T\<turnstile> Var i : t"

| ttyping_afun   : "\<lbrakk> \<Xi> f = (K', t, u)
                    ; t' = instantiate ts t
                    ; u' = instantiate ts u
                    ; list_all2 (kinding K) ts K'
                    ; K' \<turnstile> TFun t u wellformed
                    ; K \<turnstile> \<Gamma> consumed
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, (TyTrFun _, \<Gamma>) T\<turnstile> AFun f ts : TFun t' u'"

| ttyping_fun    : "\<lbrakk> \<Xi>, K', (_, [Some t]) [ n ]T\<turnstile> f : u
                    ; t' = instantiate ts t
                    ; u' = instantiate ts u
                    ; K \<turnstile> \<Gamma> consumed
                    ; K' \<turnstile> t wellformed
                    ; list_all2 (kinding K) ts K'
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, (TyTrFun n, \<Gamma>) T\<turnstile> Fun f ts : TFun t' u'"

| ttyping_app    : "\<lbrakk> ttsplit K \<Gamma> [] \<Gamma>1 [] \<Gamma>2
                    ; \<Xi>, K, \<Gamma>1 T\<turnstile> a : TFun x y
                    ; \<Xi>, K, \<Gamma>2 T\<turnstile> b : x
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> App a b : y"

| ttyping_con    : "\<lbrakk> \<Xi>, K, \<Gamma> T\<turnstile> x : t
                    ; (tag, t', Unchecked) \<in> set ts
                    ; K \<turnstile> t \<sqsubseteq> t'
                    ; K \<turnstile> TSum ts' wellformed
                    ; distinct (map fst ts)
                    ; map fst ts = map fst ts'
                    ; map (fst \<circ> snd) ts = map (fst \<circ> snd) ts'
                    ; list_all2 (\<lambda>x y. snd (snd x) \<le> snd (snd y)) ts ts'
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Con ts tag x : TSum ts'"

| ttyping_cast   : "\<lbrakk> \<Xi>, K, \<Gamma> T\<turnstile> e : TPrim (Num \<tau>)
                    ; upcast_valid \<tau> \<tau>'
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Cast \<tau>' e : TPrim (Num \<tau>')"

| ttyping_tuple  : "\<lbrakk> ttsplit K \<Gamma> [] \<Gamma>1 [] \<Gamma>2
                    ; \<Xi>, K, \<Gamma>1 T\<turnstile> t : T
                    ; \<Xi>, K, \<Gamma>2 T\<turnstile> u : U
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Tuple t u : TProduct T U"

| ttyping_split  : "\<lbrakk> ttsplit K \<Gamma> [] \<Gamma>1 [Some t, Some u] \<Gamma>2a
                    ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : TProduct t u
                    ; \<Xi>, K, \<Gamma>2a T\<turnstile> y : t'
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Split x y : t'"

| ttyping_let    : "\<lbrakk> ttsplit K \<Gamma> [] \<Gamma>1 [Some t] \<Gamma>2a
                    ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : t
                    ; \<Xi>, K, \<Gamma>2a T\<turnstile> y : u
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Let x y : u"

| ttyping_letb   : "\<lbrakk> ttsplit_bang K is \<Gamma> [] \<Gamma>1 [Some t] \<Gamma>2a
                    ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : t
                    ; \<Xi>, K, \<Gamma>2a T\<turnstile> y : u
                    ; K \<turnstile> t :\<kappa> {E}
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> LetBang is x y : u"

| ttyping_case   : "\<lbrakk> ttsplit K \<Gamma> [] \<Gamma>1 [] \<Gamma>2
                    ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : TSum ts \<comment> \<open> this must go before uses of ts \<close>
                    ; ttsplit_triv \<Gamma>2 [Some t] \<Gamma>2a [Some (TSum (tagged_list_update tag (t, Checked) ts))] \<Gamma>2b
                    ; (tag, t, Unchecked) \<in> set ts
                    ; \<Xi>, K, \<Gamma>2a T\<turnstile> a : u
                    ; \<Xi>, K, \<Gamma>2b T\<turnstile> b : u
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Case x tag a b : u"

| ttyping_esac   : "\<lbrakk> \<Xi>, K, \<Gamma> T\<turnstile> x : TSum ts
                    ; [(_, t, Unchecked)] = filter ((=) Unchecked \<circ> snd \<circ> snd) ts
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Esac x : t"

| ttyping_if     : "\<lbrakk> ttsplit K \<Gamma> [] \<Gamma>1 [] \<Gamma>2
                    ; ttsplit_triv \<Gamma>2 [] \<Gamma>2a [] \<Gamma>2b
                    ; \<Xi>, K, \<Gamma>1 T\<turnstile> x : TPrim Bool
                    ; \<Xi>, K, \<Gamma>2a T\<turnstile> a : t
                    ; \<Xi>, K, \<Gamma>2b T\<turnstile> b : t
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> If x a b : t"

| ttyping_prim   : "\<lbrakk> prim_op_type oper = (ts,t)
                    ; ts' = map TPrim ts
                    ; \<Xi>, K, \<Gamma> T\<turnstile>* args : ts'
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Prim oper args : TPrim t"

| ttyping_lit    : "\<lbrakk> K \<turnstile> \<Gamma> consumed
                    ; p = lit_type l
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, (TyTrLeaf, \<Gamma>) T\<turnstile> Lit l : TPrim p"

| ttyping_unit   : "\<lbrakk> K \<turnstile> \<Gamma> consumed
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, (TyTrLeaf, \<Gamma>) T\<turnstile> Unit : TUnit"

| ttyping_struct : "\<lbrakk> \<Xi>, K, \<Gamma> T\<turnstile>* es : ts
                    ; ns = map fst ts'
                    ; ts = map (fst \<circ> snd) ts'
                    ; list_all (\<lambda>x. snd (snd x) = Present) ts'
                    ; distinct ns
                    ; length ns = length ts
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Struct ts es : TRecord ts' Unboxed"

| ttyping_member : "\<lbrakk> \<Xi>, K, \<Gamma> T\<turnstile> e : TRecord ts s
                    ; K \<turnstile> TRecord ts s :\<kappa> {S}
                    ; f < length ts
                    ; ts ! f = (n, t, Present)
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Member e f : t"

| ttyping_take   : "\<lbrakk> ttsplit K \<Gamma> [] \<Gamma>1 [Some t, Some (TRecord ts' s)] \<Gamma>2a
                    ; \<Xi>, K, \<Gamma>1 T\<turnstile> e : TRecord ts s
                    ; ts' = ts[f := (n,t,taken)]
                    ; sigil_perm s \<noteq> Some ReadOnly
                    ; f < length ts
                    ; ts ! f = (n, t, Present)
                    ; K \<turnstile> t wellformed
                    ; S \<in> kinding_fn K t \<or> taken = Taken
                    ; \<Xi>, K, \<Gamma>2a T\<turnstile> e' : u
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Take e f e' : u"

| ttyping_put    : "\<lbrakk> ttsplit K \<Gamma> [] \<Gamma>1 [] \<Gamma>2
                    ; \<Xi>, K, \<Gamma>1 T\<turnstile> e : TRecord ts s
                    ; ts' = ts[f := (n,t,Present)]
                    ; sigil_perm s \<noteq> Some ReadOnly
                    ; f < length ts
                    ; ts ! f = (n, t, taken)
                    ; K \<turnstile> t wellformed
                    ; D \<in> kinding_fn K t \<or> taken = Taken
                    ; \<Xi>, K, \<Gamma>2 T\<turnstile> e' : t
                    \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Put e f e' : TRecord ts' s"

| ttyping_promote: "\<lbrakk> \<Xi>, K, \<Gamma> T\<turnstile> x : t' ; K \<turnstile> t' \<sqsubseteq> t \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile> Promote t x : t"

| ttyping_all_empty : "list_all (\<lambda>x. x = None) \<Gamma> \<Longrightarrow> \<Xi>, K, (TyTrLeaf, \<Gamma>) T\<turnstile>* [] : []"

| ttyping_all_cons  : "\<lbrakk> ttsplit K \<Gamma> [] \<Gamma>1 [] \<Gamma>2
                       ; ts' = (t # ts)
                       ; \<Xi>, K, \<Gamma>1 T\<turnstile> e : t
                       ; \<Xi>, K, \<Gamma>2 T\<turnstile>* es : ts
                       \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> T\<turnstile>* (e # es) : ts'"

| ttyping_named : "\<Xi>, K, T\<Gamma> T\<turnstile> e : t \<Longrightarrow> \<Xi>, K, T\<Gamma> [ n ]T\<turnstile> e : t"


inductive_cases ttyping_num     [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> e : TPrim (Num \<tau>)"
inductive_cases ttyping_bool    [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> e : TPrim Bool"
inductive_cases ttyping_varE    [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Var i : \<tau>"
inductive_cases ttyping_appE    [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> App x y : \<tau>"
inductive_cases ttyping_litE    [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Lit l : \<tau>"
inductive_cases ttyping_funE    [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Fun f ts : \<tau>"
inductive_cases ttyping_afunE   [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> AFun f ts : \<tau>"
inductive_cases ttyping_ifE     [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> If c t e : \<tau>"
inductive_cases ttyping_conE    [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Con ts t e : \<tau>"
inductive_cases ttyping_unitE   [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Unit : \<tau>"
inductive_cases ttyping_primE   [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Prim p es : \<tau>"
inductive_cases ttyping_memberE [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Member e f : \<tau>"
inductive_cases ttyping_tupleE  [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Tuple a b : \<tau>"
inductive_cases ttyping_caseE   [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Case x t m n : \<tau>"
inductive_cases ttyping_esacE   [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Esac e : \<tau>"
inductive_cases ttyping_castE   [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Cast t e : \<tau>"
inductive_cases ttyping_letE    [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Let a b : \<tau>"
inductive_cases ttyping_structE [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Struct ts es : \<tau>"
inductive_cases ttyping_letbE   [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> LetBang vs a b : \<tau>"
inductive_cases ttyping_takeE   [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Take x f e : \<tau>"
inductive_cases ttyping_putE    [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Put x f e : \<tau>"
inductive_cases ttyping_splitE  [elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Split x e : \<tau>"
inductive_cases ttyping_promoteE[elim]: "\<Xi>, K, \<Gamma> T\<turnstile> Promote \<tau>' x : \<tau>"
inductive_cases ttyping_all_emptyE [elim]: "\<Xi>, K, \<Gamma> T\<turnstile>* []       : \<tau>s"
inductive_cases ttyping_all_consE  [elim]: "\<Xi>, K, \<Gamma> T\<turnstile>* (x # xs) : \<tau>s"

lemma named_ttyping_iff_ttyping: "\<Xi>, K, T\<Gamma> T\<turnstile> e : t \<longleftrightarrow> (\<exists>n. \<Xi>, K, T\<Gamma> [ n ]T\<turnstile> e : t)"
  by (force intro: ttyping_named elim: ttyping_named.cases)

subsection {* Equivalence of Typing and TTyping *}

lemma ttyping_imp_typing:
  shows "\<Xi>, K, \<Gamma> T\<turnstile> e : u \<Longrightarrow> \<Xi>, K, (snd \<Gamma>) \<turnstile> e : u"
    and "\<Xi>, K, \<Gamma> T\<turnstile>* es : us \<Longrightarrow> \<Xi>, K, (snd \<Gamma>) \<turnstile>* es : us"
    and "\<Xi>, K, \<Gamma> [ n ]T\<turnstile> e : u \<Longrightarrow> \<Xi>, K, (snd \<Gamma>) \<turnstile> e : u"
proof (induct rule: ttyping_ttyping_all_ttyping_named.inducts)
  case (ttyping_struct \<Xi> K \<Gamma> es ts ts' ns)
  then show ?case
    by (auto intro!: typing_typing_all.intros
        simp add: list_eq_zip_iff_all_eq_pairs list_all_length prod_eqI)
next
  case (ttyping_take K \<Gamma> \<Gamma>1 t ts' s \<Gamma>2a \<Xi> e ts f n taken e' u)
  then show ?case
    by (auto simp: empty_def kinding_def
         dest!: ttsplit_imp_split
         intro!: typing_typing_all.intros)
next
  case (ttyping_put K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s ts' f n t taken e')
  then show ?case
    by (auto simp: empty_def kinding_def
         dest!: ttsplit_imp_split
         intro!: typing_typing_all.intros)
qed (auto simp: ttsplit_triv_def empty_def
         dest!: ttsplit_imp_split ttsplit_bang_imp_split_bang
         intro!: typing_typing_all.intros)

lemma typing_imp_ttyping:
  shows "\<Xi>, K, \<Gamma> \<turnstile> e : u \<Longrightarrow> \<exists>tt. \<Xi>, K, (tt, \<Gamma>) T\<turnstile> e : u"
    and "\<Xi>, K, \<Gamma> \<turnstile>* es : us \<Longrightarrow> \<exists>tt. \<Xi>, K, (tt, \<Gamma>) T\<turnstile>* es : us"
proof (induct rule: typing_typing_all.inducts)
  case (typing_struct \<Xi> K \<Gamma> es ts ns ts')
  then show ?case
    by (clarsimp, intro exI,
        force intro!: ttyping_ttyping_all_ttyping_named.intros
        simp add: nth_equalityI list_all_length distinct_conv_nth)
next
  case (typing_take K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f n t k taken e' u)
  then show ?case
    using typing_take.prems typing_take.hyps
    by (auto intro!: ttyping_ttyping_all_ttyping_named.intros simp add: kinding_def dest: split_imp_ttsplitD)
next
  case (typing_put K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f n t taken k e')
  then show ?case
    by (auto intro!: ttyping_ttyping_all_ttyping_named.intros simp add: kinding_def dest: split_imp_ttsplitD)
next
  case (typing_letb K "is" \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u k)
  then obtain tt1 tt2
    where IH_ex_elims:
      "\<Xi>, K, (tt1, \<Gamma>1) T\<turnstile> x : t"
      "\<Xi>, K, (tt2, Some t # \<Gamma>2) T\<turnstile> y : u"
    by blast
  let ?sps = "map (\<lambda>i. split_bang_tsk (i \<in> is) (\<Gamma>1 ! i) (\<Gamma>2 ! i)) [0 ..< length \<Gamma>]"
  have "ttsplit_bang K is (TyTrSplit ?sps [] tt1 [Some t] tt2, \<Gamma>) [] (tt1, \<Gamma>1) [Some t] (tt2, Some t # \<Gamma>2)"
    using typing_letb
    by (force dest: split_bang_imp_ttsplit_bang[where xs="[]" and ys="[Some t]"])
  then show ?case
    using typing_letb IH_ex_elims
    by (force intro: ttyping_letb simp add: kinding_def)
qed (fastforce dest: split_imp_ttsplitD
    intro!: ttyping_ttyping_all_ttyping_named.intros intro: supersumption
    simp add: ttsplit_triv_def)+

lemma ttyping_eq_typing:
  shows "\<Xi>, K, \<Gamma> \<turnstile> e : u \<longleftrightarrow> (\<exists>tt. \<Xi>, K, (tt, \<Gamma>) T\<turnstile> e : u)"
  by (auto dest: ttyping_imp_typing typing_imp_ttyping)

end
