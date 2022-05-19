theory Graph
imports Main
begin

declare Let_def[simp]

record 'v env =
  \<S> :: "'v \<Rightarrow> 'v set"
  explored :: "'v set"
  visited :: "'v set"
  sccs :: "'v set set"
  stack :: "'v list"

section \<open>Finite directed graphs\<close>

locale graph =
  fixes vertices :: "'v set"
    and successors :: "'v \<Rightarrow> 'v set"
  assumes vfin: "finite vertices"
    and sclosed: "\<forall>x \<in> vertices. successors x \<subseteq> vertices"

context graph

begin

abbreviation edge where
  "edge x y \<equiv> y \<in> successors x"

inductive reachable where
  reachable_refl[iff]: "reachable x x"
| reachable_succ[elim]: "\<lbrakk>edge x y; reachable y z\<rbrakk> \<Longrightarrow> reachable x z"

lemma reachable_edge: "edge x y \<Longrightarrow> reachable x y"
  by auto

lemma succ_reachable:
  assumes "reachable x y" and "edge y z"
  shows "reachable x z"
  using assms by induct auto

lemma reachable_trans:
  assumes y: "reachable x y" and z: "reachable y z"
  shows "reachable x z"
  using assms by induct auto

section \<open>Strongly connected components\<close>

definition is_subscc where
  "is_subscc S \<equiv> \<forall>x \<in> S. \<forall>y \<in> S. reachable x y"

definition is_scc where
  "is_scc S \<equiv> S \<noteq> {} \<and> is_subscc S \<and> (\<forall>S'. S \<subseteq> S' \<and> is_subscc S' \<longrightarrow> S' = S)"

lemma subscc_add:
  assumes "is_subscc S" and "x \<in> S"
      and "reachable x y" and "reachable y x"
  shows "is_subscc (insert y S)"
using assms unfolding is_subscc_def by (metis insert_iff reachable_trans)

lemma sccE:
  \<comment> \<open>Two vertices that are reachable from each other are in the same SCC.\<close>
  assumes "is_scc S" and "x \<in> S"
      and "reachable x y" and "reachable y x"
  shows "y \<in> S"
using assms unfolding is_scc_def by (metis insertI1 subscc_add subset_insertI)

lemma scc_partition:
  \<comment> \<open>Two SCCs that contain a common element are identical.\<close>
  assumes "is_scc S" and "is_scc S'" and "x \<in> S \<inter> S'"
  shows "S = S'"
  using assms unfolding is_scc_def is_subscc_def
  by (metis IntE assms(2) sccE subsetI)

section \<open>Algorithm for computing strongly connected components\<close>

function unite :: "'v \<Rightarrow> 'v \<Rightarrow> 'v env \<Rightarrow> 'v env" where
  "unite v w e =
      (if (\<S> e v = \<S> e w) then e
      else let r = hd(stack e);
               r'= hd(tl(stack e));
               joined = \<S> e r \<union> \<S> e r';
               e'= e \<lparr> stack := tl(stack e), \<S> := (\<lambda>n. if n \<in> joined then joined else \<S> e n) \<rparr>
          in unite v w e')"
  by pat_completeness auto

function dfs :: "'v \<Rightarrow> 'v env \<Rightarrow> 'v env" and dfss :: "'v \<Rightarrow> 'v set \<Rightarrow> 'v env \<Rightarrow> 'v env" where
  "dfs v e =
  (let e1 = e\<lparr>visited := visited e \<union> {v}, stack := (v # stack e)\<rparr>;
       e' = dfss v (successors v) e1
  in if v = hd(stack e')
      then e'\<lparr>sccs:=sccs e' \<union> {\<S> e' v}, explored:=explored e' \<union> (\<S> e' v), stack:=tl(stack e')\<rparr>
    else e')"
| "dfss v vs e =
   (if vs = {} then e
   else (let w = SOME x. x \<in> vs
     in (let e' = (if w \<in> explored e then e
                       else if w \<notin> visited e
                       then dfs w e
                       else unite v w e)
          in dfss v (vs-{w}) e')))"
  by pat_completeness (force+)

definition precedes ("_ \<preceq> _ in _" [100,100,100] 39) where
(* ordre de priorité, opérateur infixe, cf Old Isabelle Manuals \<rightarrow> logics \<rightarrow> "priority", "priorities"*)
  \<comment> \<open>@{text x} has an occurrence in @{text xs} that
      precedes an occurrence of @{text y}.\<close>
  "x \<preceq> y in xs \<equiv> \<exists>l r. xs = l @ (x # r) \<and> y \<in> set (x # r)"

lemma precedes_mem:
  assumes "x \<preceq> y in xs"
  shows "x \<in> set xs" "y \<in> set xs"
  using assms unfolding precedes_def by auto

lemma head_precedes:
  assumes "y \<in> set (x # xs)"
  shows "x \<preceq> y in (x # xs)"
  using assms unfolding precedes_def by force

lemma precedes_in_tail:
  assumes "x \<noteq> z"
  shows "x \<preceq> y in (z # zs) \<longleftrightarrow> x \<preceq> y in zs"
  using assms unfolding precedes_def by (auto simp: Cons_eq_append_conv)

lemma tail_not_precedes:
  assumes "y \<preceq> x in (x # xs)" "x \<notin> set xs"
  shows "x = y"
  using assms unfolding precedes_def
  by (metis Cons_eq_append_conv Un_iff list.inject set_append)

lemma split_list_precedes:
  assumes "y \<in> set (ys @ [x])"
  shows "y \<preceq> x in (ys @ x # xs)"
  using assms unfolding precedes_def
  by (metis append_Cons append_assoc in_set_conv_decomp
            rotate1.simps(2) set_ConsD set_rotate1)

lemma precedes_refl [simp]: "(x \<preceq> x in xs) = (x \<in> set xs)"
proof
  assume "x \<preceq> x in xs" thus "x \<in> set xs"
    by (simp add: precedes_mem)
next
  assume "x \<in> set xs"
  from this[THEN split_list] show "x \<preceq> x in xs"
    unfolding precedes_def by auto
qed

lemma precedes_append_left:
  assumes "x \<preceq> y in xs"
  shows "x \<preceq> y in (ys @ xs)"
  using assms unfolding precedes_def by (metis append.assoc)

lemma precedes_append_left_iff:
  assumes "x \<notin> set ys"
  shows "x \<preceq> y in (ys @ xs) \<longleftrightarrow> x \<preceq> y in xs" (is "?lhs = ?rhs")
proof
  assume "?lhs"
  then obtain l r where lr: "ys @ xs = l @ (x # r)" "y \<in> set (x # r)"
    unfolding precedes_def by blast
  then obtain us where
    "(ys = l @ us \<and> us @ xs = x # r) \<or> (ys @ us = l \<and> xs = us @ (x # r))"
    by (auto simp: append_eq_append_conv2)
  thus ?rhs
  proof
    assume us: "ys = l @ us \<and> us @ xs = x # r"
    with assms have "us = []"
      by (metis Cons_eq_append_conv in_set_conv_decomp)
    with us lr show ?rhs
      unfolding precedes_def by auto
  next
    assume us: "ys @ us = l \<and> xs = us @ (x # r)"
    with \<open>y \<in> set (x # r)\<close> show ?rhs
      unfolding precedes_def by blast
  qed
next
  assume "?rhs" thus "?lhs" by (rule precedes_append_left)
qed

lemma precedes_append_right:
  assumes "x \<preceq> y in xs"
  shows "x \<preceq> y in (xs @ ys)"
  using assms unfolding precedes_def by force

lemma precedes_append_right_iff:
  assumes "y \<notin> set ys"
  shows "x \<preceq> y in (xs @ ys) \<longleftrightarrow> x \<preceq> y in xs" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain l r where lr: "xs @ ys = l @ (x # r)" "y \<in> set (x # r)"
    unfolding precedes_def by blast
  then obtain us where
    "(xs = l @ us \<and> us @ ys = x # r) \<or> (xs @ us = l \<and> ys = us @ (x # r))"
    by (auto simp: append_eq_append_conv2)
  thus ?rhs
  proof
    assume us: "xs = l @ us \<and> us @ ys = x # r"
    with \<open>y \<in> set (x # r)\<close> assms show ?rhs
      unfolding precedes_def by (metis Cons_eq_append_conv Un_iff set_append)
  next
    assume us: "xs @ us = l \<and> ys = us @ (x # r)"
    with \<open>y \<in> set (x # r)\<close> assms 
    show ?rhs by auto \<comment> \<open>contradiction\<close>
  qed
next
  assume ?rhs thus ?lhs by (rule precedes_append_right)
qed

text \<open>
  Precedence determines an order on the elements of a list,
  provided elements have unique occurrences. However, consider
  a list such as @{term "[2,3,1,2]"}: then $1$ precedes $2$ and
  $2$ precedes $3$, but $1$ does not precede $3$.
\<close>
lemma precedes_trans:
  assumes "x \<preceq> y in xs" and "y \<preceq> z in xs" and "distinct xs"
  shows "x \<preceq> z in xs"
  using assms unfolding precedes_def
  by (smt Un_iff append.assoc append_Cons_eq_iff distinct_append 
          not_distinct_conv_prefix set_append split_list_last)

lemma precedes_antisym:
  assumes "x \<preceq> y in xs" and "y \<preceq> x in xs" and "distinct xs"
  shows "x = y"
proof -
  from \<open>x \<preceq> y in xs\<close> \<open>distinct xs\<close> obtain as bs where
    1: "xs = as @ (x # bs)" "y \<in> set (x # bs)" "y \<notin> set as"
    unfolding precedes_def by force
  from \<open>y \<preceq> x in xs\<close> \<open>distinct xs\<close> obtain cs ds where
    2: "xs = cs @ (y # ds)" "x \<in> set (y # ds)" "x \<notin> set cs"
    unfolding precedes_def by force
  from 1 2 have "as @ (x # bs) = cs @ (y # ds)"
    by simp
  then obtain zs where
    "(as = cs @ zs \<and> zs @ (x # bs) = y # ds) 
     \<or> (as @ zs = cs \<and> x # bs = zs @ (y # ds))"  (is "?P \<or> ?Q")
    by (auto simp: append_eq_append_conv2)
  then show ?thesis
  proof
    assume "?P" with \<open>y \<notin> set as\<close> show ?thesis 
      by (cases "zs") auto
  next
    assume "?Q" with \<open>x \<notin> set cs\<close> show ?thesis
      by (cases "zs") auto
  qed
qed

text \<open>
  Well-formed environments.
\<close>
definition wf_env where
  "wf_env e \<equiv>
    distinct (stack e)
  \<and> set (stack e) \<subseteq> visited e
  \<and> explored e \<subseteq> visited e
  \<and> explored e \<inter> set (stack e) = {}
  \<and> (\<forall>v w. w \<in> \<S> e v \<longleftrightarrow> (\<S> e v = \<S> e w))
  \<and> (\<forall>v \<in> set (stack e). \<forall> w \<in> set (stack e). v \<noteq> w \<longrightarrow> \<S> e v \<inter> \<S> e w = {})
  \<and> (\<forall> v. v \<notin> visited e \<longrightarrow> \<S> e v = {v})
  \<and> \<Union> {\<S> e v | v. v \<in> set (stack e)} = visited e - explored e
  \<and> (\<forall> x y. x \<preceq> y in stack e \<longrightarrow> reachable y x)
  \<and> (\<forall> x. is_subscc (\<S> e x))
  \<and> (\<forall> x \<in> explored e. \<forall> y. reachable x y \<longrightarrow> y \<in> explored e)  
  \<and> (\<forall> S \<in> sccs e. is_scc S)
"

definition sub_env where
  "sub_env e e' \<equiv> visited e \<subseteq> visited e'
                \<and> explored e \<subseteq> explored e'
                \<and> (\<forall> v. \<S> e v \<subseteq> \<S> e' v)
                \<and> (\<Union> {\<S> e v | v . v \<in> set (stack e)})
                   \<subseteq> (\<Union> {\<S> e' v | v . v \<in> set (stack e')})
"


text \<open>
  Precondition and post-condition for function dfs.
\<close>
definition pre_dfs where "pre_dfs v e \<equiv> wf_env e
                                            \<and> v \<notin> visited e
                                            \<and> (\<forall> n \<in> set (stack e). reachable n v)"

definition post_dfs where "post_dfs v prev_e e \<equiv> wf_env e
                                            \<and> (\<forall> x. reachable v x \<longrightarrow> x \<in> visited e)
                                            \<and> sub_env prev_e e
                                            \<and> (\<forall> n \<in> set (stack e). reachable n v)
                                            \<and> (set (stack e) \<subseteq> set (stack prev_e))"
                                         (* \<and> (\<forall> x. reachable v x \<longrightarrow> x \<in> explored e)" *) (* false *)

text \<open>
  Precondition for function dfss.
\<close>
definition pre_dfss where "pre_dfss v vs e \<equiv> wf_env e 
                                           \<and> v \<in> visited e
                                           \<and> vs \<subseteq> successors v
                                           \<and> (\<forall> n \<in> set (stack e). reachable n v)
                                           \<and> (stack e \<noteq> [])
                                           \<and> (\<forall> n \<in> set (stack e). reachable v n \<longrightarrow> v \<in> \<S> e n \<or> (\<exists> m \<in> vs. reachable m n))"

definition post_dfss where "post_dfss v vs prev_e e \<equiv> wf_env e
                              \<and> (\<forall> w \<in> vs. \<forall> x. reachable w x \<longrightarrow> x \<in> visited e)
                              \<and> sub_env prev_e e
                              \<and> (\<forall> n \<in> set (stack e). reachable n v)
                              \<and> (stack e \<noteq> [])
                              \<and> (\<forall> n \<in> set (stack e). reachable v n \<longrightarrow> v \<in> \<S> e n)
                              \<and> (set (stack e) \<subseteq> set (stack prev_e) \<union> {v})"
                           (* \<and> (\<forall> w \<in> vs. \<forall> x. reachable w x \<longrightarrow> x \<in> explored e)" *) (* false *)

lemma pre_dfs_pre_dfss:
  assumes "pre_dfs v e"
  shows "pre_dfss v (successors v) (e\<lparr> visited := visited e \<union> {v}, stack := v # stack e\<rparr>)"
        (is "pre_dfss v ?succs ?e'")
proof -
  have 1:"distinct (stack ?e')"
       "set (stack ?e') \<subseteq> visited ?e'"
       "explored ?e' \<subseteq> visited ?e'"
       "explored ?e' \<inter> set (stack ?e') = {}"
       "(\<forall>w z. z \<in> \<S> ?e' w \<longleftrightarrow> (\<S> ?e' w = \<S> ?e' z))"
       "(\<forall>v \<in> set (stack ?e'). \<forall> w \<in> set (stack ?e'). v \<noteq> w \<longrightarrow> \<S> ?e' v \<inter> \<S> ?e' w = {})"
       "(\<forall> v. v \<notin> visited ?e' \<longrightarrow> \<S> ?e' v = {v})"
    using assms unfolding pre_dfs_def wf_env_def by auto
  have 2:"\<Union> {\<S> ?e' v | v . v \<in> set (stack ?e')} = visited ?e' - explored ?e'"
  proof -
    have "\<Union> {\<S> ?e' v | v . v \<in> set (stack ?e')} = 
          (\<Union> {\<S> ?e' v | v . v \<in> set (stack e)}) \<union> \<S> e v"
      by auto
    also have "\<dots> = visited ?e' - explored ?e'"
      using assms unfolding pre_dfs_def wf_env_def by auto
    finally show ?thesis .
  qed

  have 3:"\<forall> x y. x \<preceq> y in stack ?e' \<longrightarrow> reachable y x"
  proof (clarify)
    fix x y
    assume "x \<preceq> y in stack ?e'"
    show "reachable y x"
    proof (cases "x=v")
      assume "x=v"
      have "\<forall> y. v \<preceq> y in stack ?e' \<longrightarrow> reachable y v"
      proof (cases "stack e = []")
        assume "stack e = []"
        hence "stack ?e' = [v]" by simp
        thus ?thesis
          using precedes_mem(2) by fastforce
      next
        assume "stack e \<noteq> []"
        have reach_hd:"reachable (hd (stack e)) v"
          using assms \<open>stack e \<noteq> []\<close> unfolding pre_dfs_def by force
        show ?thesis
        proof (clarify)
          fix y
          assume "v \<preceq> y in stack ?e'"
          show "reachable y v"
          proof (cases "y = v")
            assume "y = v"
            thus ?thesis
              by blast
          next
            assume "y \<noteq> v"
            hence "y \<in> set(stack e)"
              using \<open>v \<preceq> y in stack (e\<lparr>visited := visited e \<union> {v}, stack := v # stack e\<rparr>)\<close> precedes_mem(2) by fastforce 
            hence "hd(stack e) \<preceq> y in stack e"
              using \<open>stack e \<noteq> []\<close> head_precedes list.exhaust list.sel(1) by metis
            hence "reachable y (hd(stack e))"
              using assms pre_dfs_def wf_env_def by blast
            thus ?thesis using reach_hd reachable_trans by blast
          qed
        qed
      qed
      thus ?thesis
        using \<open>x = v\<close> \<open>x \<preceq> y in stack ?e'\<close> by blast 
    next
      assume "x \<noteq> v"
      have "x \<preceq> y in stack e"
        using \<open>x \<noteq> v\<close> \<open>x \<preceq> y in stack ?e'\<close> precedes_in_tail by fastforce
      thus ?thesis
        using assms pre_dfs_def wf_env_def by blast 
    qed
  qed

  have 4:"\<forall> x. is_subscc (\<S> ?e' x)" using assms
    unfolding pre_dfs_def wf_env_def by simp

  have 5:"\<forall> x \<in> explored ?e'. \<forall> y. reachable x y \<longrightarrow> y \<in> explored ?e'"
  proof -
    have "explored ?e' = explored e" by simp
    then show ?thesis using assms unfolding wf_env_def
      by (simp add: pre_dfs_def wf_env_def) 
  qed

  have 6:"\<forall> S \<in> sccs ?e'. is_scc S"
  proof (clarify)
    fix S
    assume asm:"S \<in> sccs ?e'"
    have "sccs e = sccs ?e'" by simp
    thus "is_scc S" using assms
      using asm pre_dfs_def wf_env_def by blast
  qed

  have wfenv:"wf_env ?e'" using 1 2 3 4 5 6 unfolding wf_env_def
    by blast

  have subsucc:"v \<in> visited ?e'" by simp

  have reachstack:"\<forall> n \<in> set (stack ?e'). reachable n v"
    by (simp add: \<open>\<forall>x y. x \<preceq> y in stack ?e' \<longrightarrow> reachable y x\<close> head_precedes)

  have succ:"?succs \<subseteq> successors v" by simp

  have notempty: "stack ?e' \<noteq> []"
    by simp

  then show ?thesis
    using pre_dfss_def reachstack subsucc wfenv
    by (smt (verit, best) "1"(5) reachable.cases succ)
qed

lemma pre_dfss_pre_dfs:
  fixes w
  assumes "pre_dfss v vs e" and "w \<notin> visited e" and "w \<in> vs"
  shows "pre_dfs w e" 
proof -
  have "wf_env e"
    using assms(1) pre_dfss_def by fastforce
  thus ?thesis
    by (meson assms(1) assms(2) assms(3) graph.pre_dfss_def graph_axioms in_mono pre_dfs_def succ_reachable) 
qed

lemma pre_dfs_implies_post_dfs:
  fixes v e
  defines "e1 \<equiv> e\<lparr>visited := visited e \<union> {v}, stack := (v # stack e)\<rparr>"
  defines "e' \<equiv> dfss v (successors v) e1"
  assumes 1: "pre_dfs v e"
      and 2: "dfs_dfss_dom (Inl(v, e))"
      and 3: "post_dfss v (successors v) e1 e'"
  shows "post_dfs v e (dfs v e)"
proof (cases "v = hd(stack e')")
  case True
  hence "stack e' = v # tl(stack e')"
    by (metis "3" graph.post_dfss_def graph_axioms list.exhaust_sel)
  hence notempty: "v \<in> set (stack e')"
    by (metis list.set_intros(1))
  with 2 have e2:"dfs v e = e'\<lparr>sccs:=sccs e' \<union> {\<S> e' v}, 
                            explored:=explored e' \<union> (\<S> e' v), 
                            stack:=tl(stack e')\<rparr>" (is "_ = ?e2")
    unfolding e1_def e'_def
    using True assms(1) assms(2) dfs.psimps by force
  have stack:"stack ?e2 = tl (stack e')" by simp

  have sub:"sub_env e e1" unfolding sub_env_def
    using e1_def by auto
  moreover have subenv:"sub_env e ?e2" 
  proof -
    have e:"visited e \<subseteq> visited e'"
      by (meson "3" in_mono post_dfss_def sub sub_env_def subsetI)
    have e':"visited e' \<subseteq> visited ?e2" unfolding e'_def
      by (simp add: dfs.psimps)
    from e and e' have visited:"visited e \<subseteq> visited ?e2"
      by blast

    have e:"explored e \<subseteq> explored e'"
      by (metis "3" post_dfss_def sub sub_env_def subset_trans)
    have e':"explored e' \<subseteq> explored ?e2" unfolding e'_def
      by (simp add: dfs.psimps)
    from e and e' have explored:"explored e \<subseteq> explored ?e2"
      by blast

    have S:"\<forall> v. \<S> e v \<subseteq> \<S> ?e2 v"
    proof -
      have e:"\<forall> v. \<S> e v \<subseteq> \<S> e' v"
        by (meson "3" post_dfss_def sub sub_env_def subset_trans)
      have e':"\<forall> v. \<S> e' v \<subseteq> \<S> ?e2 v"
        by (simp add: dfs.psimps)
      from e and e' have "\<forall> v. \<S> e v \<subseteq> \<S> ?e2 v"
        by blast
      thus ?thesis by simp
    qed

    have union:"\<Union> {\<S> e n | n. n \<in> set (stack e)} \<subseteq> \<Union> {\<S> ?e2 n | n. n \<in> set (stack ?e2)}" sorry


    from visited explored S union show ?thesis
      using sub_env_def by blast
  qed

  have Se'e2_eq:"\<forall> x. \<S> e' x = \<S> ?e2 x"
    by simp

  moreover have wfenv:"wf_env ?e2"
  proof -
    have "distinct (stack ?e2)"
      using 3 by (auto simp: post_dfss_def wf_env_def distinct_tl)
  
    moreover have "set (stack ?e2) \<subseteq> visited ?e2"
    proof -
      have "set (stack ?e2) = set (tl (stack e'))" by simp
      also have "\<dots> \<subseteq> visited e'"
        by (smt (verit, del_insts) "3" \<open>stack e' = v # tl (stack e')\<close> order_trans post_dfss_def set_subset_Cons wf_env_def)
      finally show ?thesis by simp
    qed
  
    moreover have "explored ?e2 \<subseteq> visited ?e2"
    proof -
      from 3 have "explored e' \<subseteq> visited e'"
        unfolding post_dfss_def wf_env_def by simp
      moreover have "\<S> e' v \<subseteq> visited e'"
        by (smt (verit, best) "3" graph.post_dfss_def graph_axioms notempty singletonD subsetD subsetI wf_env_def) 
      ultimately show ?thesis by simp
    qed
  
    moreover have "explored ?e2 \<inter> set (stack ?e2) = {}"
    proof -
      {
        fix w
        assume w1:"w\<in> explored ?e2" and w2:"w \<in> set(stack ?e2)"
        have "explored ?e2 = explored e' \<union> \<S> e' v" "stack ?e2 = tl(stack e')" by auto
        have False
        proof(cases "w\<in> explored e'")
          case True
          have "w \<in> explored e' \<inter> set(stack e')"
            by (metis Int_iff \<open>stack ?e2 = tl (stack e')\<close> \<open>w \<in> explored e'\<close> empty_iff list.set_sel(2) notempty set_empty w2) 
          thus ?thesis
            by (smt (verit, ccfv_threshold) "3" emptyE post_dfss_def wf_env_def)
        next
          case False
          have "w \<in> \<S> e' v"
            using False w1 by auto 
          have "w \<in> set(tl(stack e'))"
            using w2 by force
          hence "w \<noteq> v"
            by (smt (verit, del_insts) "3" \<open>stack e' = v # tl (stack e')\<close> distinct.simps(2) graph.post_dfss_def graph_axioms wf_env_def)
          hence "w \<in> \<S> e' w \<inter> \<S> e' v"
            using "3" \<open>w \<in> \<S> e' v\<close> post_dfss_def wf_env_def by fastforce
          thus ?thesis using 3 post_dfss_def wf_env_def
            by (smt (verit) \<open>w \<in> set (tl (stack e'))\<close> \<open>w \<noteq> v\<close> empty_iff list.set_sel(2) notempty)
        qed
      }
      hence "set (tl (stack e')) \<inter> \<S> e' v = {}" by auto
      moreover have "stack ?e2 = tl(stack e')" by simp
      moreover have "explored ?e2 = explored e' \<union> \<S> e' v" by simp
      moreover have "explored e' \<inter> set (stack e') = {}"
        using 3 post_dfss_def wf_env_def graph_axioms
        by (smt (verit, ccfv_threshold))
      ultimately show ?thesis
        by (smt (verit, ccfv_threshold) Un_iff disjoint_iff empty_iff list.set(1) list.set_sel(2) notempty)
    qed
  
    moreover have "\<forall>v w. w \<in> \<S> ?e2 v \<longleftrightarrow> (\<S> ?e2 v = \<S> ?e2 w)"
    proof -
      have lr: "\<forall>v w. w \<in> \<S> ?e2 v \<longrightarrow> (\<S> ?e2 v = \<S> ?e2 w)"
      proof (clarify)
        fix v w
        assume w: "w \<in> \<S> ?e2 v"
        {
          fix x
          assume x_sev:"x \<in> \<S> ?e2 v"
          have "x \<in> \<S> ?e2 w"
          proof (cases "x\<in>\<S> e' w")
            case True
            hence "x\<in>\<S> e' v" using e'_def
              using x_sev by fastforce 
            then show ?thesis
              by (simp add: True) 
          next
            case f:False
            have False
            proof (cases "x \<in> \<S> e' v")
              case True
              have "w \<in> \<S> e' v"
                using w by auto
              hence "\<S> e' v = \<S> e' w"
                by (smt (verit, del_insts) "3" graph.post_dfss_def graph_axioms wf_env_def)
             thus ?thesis
                using True f by auto 
            next
              case False
              have "\<S> e' v = \<S> ?e2 v" by simp
              hence "x \<notin> \<S> ?e2 v"
                using False by blast 
              then show ?thesis
                using x_sev by blast 
            qed
            thus ?thesis
              by blast 
          qed
        }
        moreover
        {
          fix x
          assume x:"x \<in> \<S> ?e2 w"
          have "x \<in> \<S> ?e2 v" 
          proof (cases "w \<in> \<S> e' v")
            case True
            have "\<S> e' w = \<S> e' v"
              by (smt (verit, del_insts) "3" True graph.post_dfss_def graph_axioms wf_env_def)
            hence "\<S> ?e2 v = \<S> ?e2 w"
              by simp
            thus ?thesis using x by simp
          next
            case False
            have False
            proof -
              from Se'e2_eq have "w \<notin> \<S> ?e2 v"
                using False by blast
              thus ?thesis
                using w by blast 
            qed
            thus ?thesis
              by blast 
          qed
        }
        ultimately show "\<S> ?e2 v = \<S> ?e2 w"
          by blast
      qed
      moreover have rl: "\<forall>v w. (\<S> ?e2 v = \<S> ?e2 w) \<longrightarrow> w \<in> \<S> ?e2 v"
      proof (clarify)
        fix v w
        assume S: "\<S> ?e2 v = \<S> ?e2 w"
        have "w \<in> \<S> ?e2 w"
        proof (cases "w \<in> \<S> e w")
          case True
          then show ?thesis
            using "3" graph.post_dfss_def graph_axioms wf_env_def by fastforce
        next
          case False
          have False
            using "1" False graph.pre_dfs_def graph_axioms wf_env_def by fastforce
          thus ?thesis
            by blast 
        qed
        thus "w \<in> \<S> ?e2 v" using S
          by blast
      qed
      from lr rl show ?thesis by blast
    qed
  
    moreover have onStackOneRepr:"\<forall>v w. (v \<in> set (stack ?e2) \<and> w \<in> set (stack ?e2) \<and> v \<noteq> w) \<longrightarrow> (\<S> ?e2 v \<inter> \<S> ?e2 w = {})"
    proof (clarify)
      fix v w
      assume asm: "v \<in> set (stack ?e2)" "w \<in> set (stack ?e2)" "v \<noteq> w"
      from asm have v':"v \<in> set (stack e')"
        by (metis empty_set insert_absorb insert_not_empty list.set_sel(2) notempty select_convs(5) surjective update_convs(5))
      from asm have w':"w \<in> set (stack e')"
        by (metis empty_set insert_absorb insert_not_empty list.set_sel(2) notempty select_convs(5) surjective update_convs(5))
      from v' w' have "\<S> e' v \<inter> \<S> e' w = {}" using assms(5)
        by (simp add: asm post_dfss_def wf_env_def)
      then show "\<S> ?e2 v \<inter> \<S> ?e2 w = {}"
        by simp
    qed
  
    moreover have"(\<forall> v. v \<notin> visited ?e2 \<longrightarrow> \<S> ?e2 v = {v})"
    proof (clarify)
      fix v
      assume "v \<notin> visited ?e2"
      hence "v \<notin> visited e'"
        by simp
      hence 1:"\<S> e' v = {v}" using assms(5)
        by (simp add: post_dfss_def wf_env_def)
      from 1 Se'e2_eq show "\<S> ?e2 v = {v}" by blast
    qed
  
    moreover have "\<Union> {\<S> ?e2 v | v . v \<in> set (stack ?e2)} = visited ?e2 - explored ?e2"
    proof -
      have 1:"\<Union> {\<S> e' v | v . v \<in> set (stack e')} = visited e' - explored e'" using assms(5)
        by (simp add: post_dfss_def wf_env_def)
      also have "... = \<Union> {\<S> ?e2 v | v . v \<in> set (stack e')}" using Se'e2_eq
        using calculation by auto
      have stack:"stack ?e2 = tl(stack e')" by simp
      with True stack have stacke':"set (stack e') = set (stack ?e2)  \<union> {v}"
        by (metis Un_insert_right empty_iff empty_set list.exhaust_sel list.simps(15) notempty sup_bot.right_neutral)
      hence 2:"\<Union> {\<S> ?e2 v | v . v \<in> set (stack e')} = (\<Union>{\<S> ?e2 v | v . v \<in> set (stack ?e2)}) \<union> (\<S> ?e2 v)" by auto
      have exploredD:"explored e' = explored ?e2 - (\<S> ?e2 v)"
      proof -
        have "explored ?e2 = explored e' \<union> (\<S> ?e2 v)" by simp
        moreover have "explored e' \<inter> (\<S> ?e2 v) = {}"
          using 1 2 by auto
        thus ?thesis
          by auto
      qed
      hence "visited e' - explored e' = visited ?e2 - (explored ?e2 - (\<S> ?e2 v))"
        by simp
      hence "(\<Union>{\<S> ?e2 v | v . v \<in> set (stack ?e2)}) \<union> (\<S> ?e2 v) = visited ?e2 - (explored ?e2 - (\<S> ?e2 v))" using 1 2
        by simp
      moreover have disjoint:"(\<Union>{\<S> ?e2 v | v . v \<in> set (stack ?e2)}) \<inter> (\<S> ?e2 v) = {}"
      proof -
        have "\<forall> w. w \<in> set (stack ?e2) \<longrightarrow> \<S> ?e2 w \<inter> \<S> ?e2 v = {}" using onStackOneRepr
          by (smt (verit, best) "3" Se'e2_eq True Un_empty Un_iff distinct.simps(2) graph.wf_env_def graph_axioms hd_Cons_tl insert_not_empty notempty post_dfss_def set_empty stack stacke')
        thus ?thesis
          by blast
      qed
      hence strong:"(\<Union>{\<S> ?e2 v | v . v \<in> set (stack ?e2)}) \<union> (\<S> ?e2 v) = (visited ?e2 - explored ?e2) \<union> (\<S> ?e2 v)"
        using calculation(2) by auto
      have magic:"(visited ?e2 - explored ?e2) \<inter> (\<S> ?e2 v) = {}" using 1 "2" exploredD
        by force
      thus ?thesis using strong magic
        by (smt (verit, best) Int_Un_distrib Int_commute Un_Int_eq(3) disjoint)
    qed
    
    moreover have "\<forall> x y. x \<preceq> y in stack ?e2 \<longrightarrow> reachable y x"
    proof (clarify)
      fix x y
      assume asm:"x \<preceq> y in stack ?e2"
      have reachable:"\<forall> x y. x \<preceq> y in stack e' \<longrightarrow> reachable y x" using assms(5) post_dfss_def wf_env_def
        by fastforce
      have "x \<preceq> y in stack e'" using stack asm
        by (metis \<open>stack e' = v # tl (stack e')\<close> emptyE head_precedes list.set_sel(2) notempty precedes_in_tail precedes_mem(2) set_empty)
      thus "reachable y x" using reachable by blast 
    qed
  
    moreover have "\<forall> x. is_subscc (\<S> ?e2 x)" using assms(5)
      by (simp add: post_dfss_def wf_env_def)

    moreover have "\<forall> x \<in> explored ?e2. \<forall> y. reachable x y \<longrightarrow> y \<in> explored ?e2"
    proof (clarify)
      fix x y
      assume asm:"x \<in> explored ?e2" "reachable x y"
      show "y \<in> explored ?e2"
      proof (cases "x \<in> explored e'")
        case True
        then show ?thesis using 3 wf_env_def unfolding wf_env_def
          by (simp add: asm(2) post_dfss_def wf_env_def)
      next
        from notempty have stacke':"v \<in> set (stack e')"
          by blast
        case False
        hence "x \<in> \<S> e' v" using asm
          by simp
        hence "reachable v y" using asm(2) assms(5)
          by (metis Se'e2_eq calculation(10) calculation(5) is_subscc_def reachable_trans)
        hence visitedy:"y \<in> visited e'" using assms(5) stacke' unfolding post_dfss_def
          by (smt (verit, best) in_mono reachable.cases wf_env_def)
        then show ?thesis
        proof (cases "y \<in> explored e'")
          case True
          then show ?thesis
            by simp
        next
          case False
          from False visitedy have "y \<in> \<Union> {\<S> e' v | v. v \<in> set (stack e')}" using wf_env_def[of e'] assms(5)
            by (simp add: post_dfss_def)
          then obtain n where ndef:"n \<in> set (stack e') \<and> (y \<in> \<S> e' n)"
            by force
          have "reachable y n" using ndef
            using calculation(10) calculation(5) is_subscc_def by force
          hence "reachable v n"
            using \<open>reachable v y\<close> reachable_trans by blast
          hence "v \<in> \<S> e' n" using assms(5) post_dfss_def
            using ndef by blast
          moreover have "v \<in> \<S> e' v"
            using Se'e2_eq \<open>\<forall>va w. (w \<in> \<S> ?e2 va) \<longleftrightarrow> (\<S> ?e2 va = \<S> ?e2 w)\<close> by blast
          hence "v = n" using notempty assms(5) wf_env_def[of e'] post_dfss_def
            using calculation ndef by blast
          hence "y \<in> \<S> e' v"
            using ndef by blast
          then show ?thesis
            by simp
        qed
      qed
    qed

    moreover have "\<forall> S \<in> sccs ?e2. is_scc S"
    proof (clarify)
      fix S
      assume asm:"S \<in> sccs ?e2"
      show "is_scc S"
      proof (cases "S = \<S> e' v")
        case True
        hence nemp:"S \<noteq> {}"
          using Se'e2_eq calculation(5) by blast
        have subscc:"is_subscc S"
          using True calculation(10) by fastforce
        {
          assume contrad:"\<not> is_scc S"
          then obtain S' where S'_def:"S' \<noteq> S \<and> S \<subseteq> S' \<and> is_subscc S'" unfolding is_scc_def
            using nemp subscc by blast
          then obtain x where "x \<in> S' \<and> x \<notin> S"
            by blast
          hence xv:"reachable v x \<and> reachable x v"
            by (metis Se'e2_eq True S'_def calculation(5) in_mono is_subscc_def)
          have "\<S> e' v =  \<S> e' x"
          proof (cases "x \<in> set (stack e')")
            case True
            then show ?thesis using xv
              by (metis "3" Se'e2_eq calculation(5) post_dfss_def)
          next
            case False
            have "x \<in> explored e'"
              using True \<open>x \<in> S' \<and> x \<notin> S\<close> calculation(11) calculation(5) xv by auto
            from assms(5) have "\<forall> x \<in> explored e'. \<forall> y. reachable x y \<longrightarrow> y \<in> explored e'" using post_dfss_def unfolding wf_env_def
              by (simp add: post_dfss_def wf_env_def)
            hence "v \<in> explored e'" using False
              using \<open>x \<in> explored e'\<close> xv by blast
            hence False using notempty wf_env_def assms(5) unfolding post_dfss_def
              by fastforce
            thus ?thesis
              by simp
          qed
          then have "is_scc S"
            using Se'e2_eq True \<open>x \<in> S' \<and> x \<notin> S\<close> calculation(5) by blast
        }
        then show ?thesis
          by blast
      next
        case False
        hence "S \<in> sccs e'" using asm
          by simp
        then show ?thesis
          using assms(5) post_dfss_def wf_env_def by fastforce
      qed
    qed
    
    ultimately show ?thesis unfolding wf_env_def
      by meson
  qed

  moreover have reachable_visited:"\<forall> x. reachable v x \<longrightarrow> x \<in> visited ?e2"
  proof (clarify)
    fix x
    assume "reachable v x"
    then show "x \<in> visited ?e2" using 3 post_dfss_def reachable.cases notempty wf_env_def
      by (smt (verit, best) ext_inject subset_iff surjective update_convs(2) update_convs(4) update_convs(5))
  qed

  moreover have stack_reachable:"\<forall> n \<in> set (stack ?e2). reachable n v" using assms stack
    by (metis list.set_sel(2) post_dfss_def)

  moreover have "set (stack ?e2) \<subseteq> set (stack e)" sorry

  ultimately show ?thesis using subenv wfenv reachable_visited stack_reachable e2 unfolding post_dfs_def
    by metis 
next
  case False
  with 2 have e':"dfs v e = e'"
    unfolding e1_def e'_def by (simp add: dfs.psimps)

  moreover have wfenv:"wf_env e'" using 3 post_dfss_def by metis

  moreover have subenv:"sub_env e e'"
  proof -
    have "sub_env e e1"
      unfolding sub_env_def
      using e1_def by auto
    thus ?thesis
      by (meson "3" post_dfss_def sub_env_def subset_trans)
  qed

  moreover have reachable_visited:"(\<forall> x. reachable v x \<longrightarrow> x \<in> visited e')"
  proof (clarify)
    fix x
    assume asm:"reachable v x"
    show "x \<in> visited e'"
    proof (cases "x = v")
      case True
      have "visited e1 \<subseteq> visited e'"
        using 3 dfs.psimps dfss.psimps
        unfolding post_dfss_def
        by (metis sub_env_def)
      have v:"v \<in> visited e1"
        by (simp add: e1_def)
      thus ?thesis
        using True \<open>visited e1 \<subseteq> visited e'\<close> by auto
    next
      case False
      obtain w where "w \<in> (successors v) \<and> reachable w x" using False
        by (meson asm reachable.cases)
      then show ?thesis using 3
        by (metis post_dfss_def)
    qed
  
  qed

  moreover have stack_visited:"\<forall> n \<in> set (stack e'). reachable n v"
    using "3" post_dfss_def by force

  moreover have "set (stack e') \<subseteq> set (stack e)" sorry

  ultimately show ?thesis unfolding post_dfs_def
    by blast
qed

lemma partial_correctness:
  shows
  "\<lbrakk>dfs_dfss_dom (Inl(v,e)); pre_dfs v e\<rbrakk> \<Longrightarrow> post_dfs v e (dfs v e)"
  "\<lbrakk>dfs_dfss_dom (Inr(v,vs,e)); pre_dfss v vs e\<rbrakk> \<Longrightarrow> post_dfss v vs e (dfss v vs e)"
proof (induct rule: dfs_dfss.pinduct)
  fix v e
  assume dom:"dfs_dfss_dom (Inl(v,e))"
     and predfs:"pre_dfs v e"
     and prepostdfss:"\<And>e1. \<lbrakk> e1 = e \<lparr>visited := visited e \<union> {v}, stack := v # stack e\<rparr>; pre_dfss v (successors v) e1 \<rbrakk>
               \<Longrightarrow> post_dfss v (successors v) e1 (dfss v (successors v) e1)"
  show "post_dfs v e (dfs v e)" thm pre_dfs_implies_post_dfs
  proof (cases "v \<in>  set (stack (dfss v (successors v) e \<lparr>visited := visited e \<union> {v}, stack := v # stack e\<rparr>))")
    case True
    then show ?thesis
      using dom pre_dfs_implies_post_dfs pre_dfs_pre_dfss predfs prepostdfss by blast
  next
    case False
    then show ?thesis
      by (meson dom pre_dfs_implies_post_dfs pre_dfs_pre_dfss predfs prepostdfss)
  qed
next
  fix v vs e
  assume dom:"dfs_dfss_dom (Inr(v,vs,e))"
     and predfss:"pre_dfss v vs e"
     and prepostdfs:"\<And>w. \<lbrakk> vs \<noteq> {}; w = (SOME x. x \<in> vs); w \<notin> explored e; w \<notin> visited e; pre_dfs w e \<rbrakk> \<Longrightarrow> post_dfs w e (dfs w e)"
     and prepostdfss:"\<And>w e'. \<lbrakk> vs \<noteq> {}; w = (SOME x. x \<in> vs); e' = (if w \<in> explored e then e else if w \<notin> visited e then dfs w e else unite v w e);pre_dfss v (vs - {w}) e' \<rbrakk> \<Longrightarrow> post_dfss v (vs - {w}) e' (dfss v (vs - {w}) e')"
  show "post_dfss v vs e (dfss v vs e)"
  proof (cases "vs = {}")
    case True
    then show ?thesis
      using dom dfss.psimps graph.pre_dfss_def graph.sub_env_def graph_axioms post_dfss_def predfss by fastforce
  next
    case vs_case:False
    define w where "w = (SOME x. x \<in> vs)"
    define e' where "e' = (if w \<in> explored e then e else if w \<notin> visited e then dfs w e else unite v w e)"
    show ?thesis
    proof (cases "w \<in> explored e")
      case True
      hence "dfss v vs e = dfss v (vs - {w}) e'" using dfss.psimps e'_def True
        by (simp add: dom vs_case w_def)

      moreover from True have env_eq:"e' = e" using e'_def
        by simp
      hence "pre_dfss v (vs - {w}) e'"
        by (smt (verit, best) Diff_empty Diff_insert0 Diff_subset IntI True empty_iff insertE insert_Diff order_trans pre_dfss_def predfss wf_env_def)
      then have post:"post_dfss v (vs - {w}) e' (dfss v (vs - {w}) e')"
        using True env_eq prepostdfss vs_case w_def by auto

      moreover have wfenv:"wf_env (dfss v vs e)"
        using calculation(1) post post_dfss_def by auto
      moreover have reach:"\<forall> u \<in> vs. \<forall> x. reachable u x \<longrightarrow> x \<in> visited (dfss v vs e)"
      proof (clarify)
        fix u x
        assume asm:"u \<in> vs" "reachable u x"
        show "x \<in> visited (dfss v vs e)"
        proof (cases "u = w")
          case True
          then show ?thesis using \<open>w \<in> explored e\<close> asm wfenv unfolding wf_env_def
            by (metis calculation(1) env_eq in_mono post post_dfss_def sub_env_def)
        next
          case False
          hence u:"u \<in> vs - {w}"
            by (simp add: asm(1))
          hence "w \<in> visited (dfss v (vs - {w}) e)"
            by (smt (verit, del_insts) True env_eq graph.post_dfss_def graph_axioms in_mono post sub_env_def wf_env_def)
          then show  ?thesis using False asm dfss.psimps dom env_eq post post_dfss_def vs_case w_def
            by (metis u calculation(1))
        qed
      qed

      moreover have "dfss v vs e = dfss v (vs - {w}) e'" using dfss.psimps e'_def True
        using calculation(1) by blast

      ultimately show ?thesis
        by (simp add: env_eq post_dfss_def)
    next
      case notexplored:False
      then show ?thesis
      proof (cases "w \<notin> visited e")
        case True
        hence "e' = dfs w e" using e'_def notexplored
          by auto
        hence postdfsw:"post_dfs w e e'"
          using True notexplored pre_dfss_pre_dfs predfss prepostdfs some_in_eq vs_case w_def by blast
        have "dfss v vs e = dfss v (vs - {w}) e'"
          using True dfss.psimps dom e'_def notexplored vs_case w_def by force
        have "pre_dfss v (vs - {w}) e'"
        proof -
          from postdfsw have "wf_env e'"
            using post_dfs_def by blast
          moreover have "v \<in> visited e'"
            by (metis graph.post_dfs_def graph_axioms in_mono postdfsw pre_dfss_def predfss sub_env_def)
          moreover have "vs - {w} \<subseteq> successors v"
            by (metis Diff_subset pre_dfss_def predfss subset_trans)
          
          moreover have "\<forall> n \<in> set (stack e'). reachable n v" using postdfsw post_dfs_def
            by (metis pre_dfss_def predfss subset_iff)
          
          moreover have "stack e' \<noteq> []"
          proof (rule ccontr)
            assume "\<not> stack e' \<noteq> []"
            have "reachable v w" using w_def sorry
            then show False sorry
          qed
          
          moreover have "\<forall> n \<in> set (stack e'). reachable v n \<longrightarrow> v \<in> \<S> e' n \<or> (\<exists> m \<in> vs - {w}. reachable m n)" sorry

          ultimately show ?thesis
            by (simp add: pre_dfss_def)
        qed
        then show ?thesis sorry
      next
        case False
        then show ?thesis sorry
        (*proof -
          have wfenv: "wf_env e'" sorry
          have reachvisited:"\<forall> w \<in> vs. \<forall> x. reachable w x \<longrightarrow> x \<in> visited e'" sorry
          have subenv:"sub_env e e'" sorry
          have stackreach:"\<forall> n \<in> set (stack e'). reachable n v" sorry
          have nemp:"stack e' \<noteq> []" sorry
          have reachS:"\<forall> n \<in> set (stack e). reachable v n \<longrightarrow> v \<in> \<S> e n" sorry
        qed*)
      qed
    qed
  qed
qed


end
end