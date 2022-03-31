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
(* is_scc translates the fact of being a maximal set of vertices possessing the property of being strongly connected. *)
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
(*
pat_completeness : ensures that the function is complete, i.e. every entry in the domain is covered.
auto : proves that unite is actually a function, so that for two equal entries, the computed results for both entries are equal.
The termination is not proved.
*)

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

(*
pat_completeness : completes all patterns 
force : proves that dfs and dfss are functions. Method auto cannot terminate because of the mutual recursion.
The termination is not proved.
*)

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
  "

definition sub_env where
  "sub_env e e' \<equiv> visited e \<subseteq> visited e'
                \<and> explored e \<subseteq> explored e'
                \<and> (\<forall> v. \<S> e v \<subseteq> \<S> e' v)"


text \<open>
  Precondition and post-condition for function dfs.
\<close>
definition pre_dfs where "pre_dfs v e \<equiv> wf_env e \<and> v \<notin> visited e \<and> ((stack e = []) \<or> reachable (hd (stack e)) v)"

definition post_dfs where "post_dfs v e \<equiv> wf_env e
                                            \<and> (\<forall> x. reachable v x \<longrightarrow> x \<in> visited e)
                                            \<and> sub_env e (dfs v e)"
                                         (* \<and> (\<forall> x. reachable v x \<longrightarrow> x \<in> explored e)" *) (* false *)

text \<open>
  Precondition for function dfss.
\<close>
definition pre_dfss where "pre_dfss v vs e \<equiv> wf_env e 
                                           \<and> v \<in> visited e
                                           \<and> v \<in> set (stack e)
                                           \<and> vs \<subseteq> successors v"

definition post_dfss where "post_dfss v vs e \<equiv> wf_env e
                              \<and> (\<forall> w \<in> vs. \<forall> x. reachable w x \<longrightarrow> x \<in> visited e)
                              \<and> sub_env e (dfss v vs e)"
                           (* \<and> (\<forall> w \<in> vs. \<forall> x. reachable w x \<longrightarrow> x \<in> explored e)" *) (* false *)

lemma pre_dfs_pre_dfss:
  assumes "pre_dfs v e"
  shows "pre_dfss v (successors v) (e \<lparr> visited := visited e \<union> {v}, stack := v # stack e\<rparr>)"
        (is "pre_dfss v ?succs ?e'")
proof -
  have "distinct (stack ?e')"
       "set (stack ?e') \<subseteq> visited ?e'"
       "explored ?e' \<subseteq> visited ?e'"
       "explored ?e' \<inter> set (stack ?e') = {}"
       "(\<forall>w z. z \<in> \<S> ?e' w \<longleftrightarrow> (\<S> ?e' w = \<S> ?e' z))"
       "(\<forall>v \<in> set (stack ?e'). \<forall> w \<in> set (stack ?e'). v \<noteq> w \<longrightarrow> \<S> ?e' v \<inter> \<S> ?e' w = {})"
       "(\<forall> v. v \<notin> visited ?e' \<longrightarrow> \<S> ?e' v = {v})"
    using assms unfolding pre_dfs_def wf_env_def by auto
  moreover have "\<Union> {\<S> ?e' v | v . v \<in> set (stack ?e')} = visited ?e' - explored ?e'"
  proof -
    have "\<Union> {\<S> ?e' v | v . v \<in> set (stack ?e')} = 
          (\<Union> {\<S> ?e' v | v . v \<in> set (stack e)}) \<union> \<S> e v"
      by auto
    also have "\<dots> = visited ?e' - explored ?e'"
      using assms unfolding pre_dfs_def wf_env_def by auto
    finally show ?thesis .
  qed
  moreover have "\<forall> x y. x \<preceq> y in stack ?e' \<longrightarrow> reachable y x"
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

  have "v \<in> visited ?e'" by simp
  ultimately show ?thesis
    using \<open>\<forall>x y. x \<preceq> y in stack ?e' \<longrightarrow> reachable y x\<close> unfolding wf_env_def pre_dfs_def pre_dfss_def by fastforce 
qed

lemma pre_dfss_pre_dfs:
  fixes w
  assumes "pre_dfss v vs e" and "w \<notin> visited e" and "w \<in> vs"
  shows "pre_dfs w e" 
proof -
  have "wf_env e"
    using assms(1) pre_dfss_def by fastforce
  have "reachable v w"
    using assms(1) assms(3) pre_dfss_def reachable_edge by blast 
  have "((stack e = []) \<or> reachable (hd (stack e)) w)"
  proof (cases "stack e = []")
    assume "stack e = []"
    thus ?thesis by simp
  next
    assume "stack e \<noteq> []"
    have "reachable (hd(stack e)) w"
    proof (cases "v = hd(stack e)")
      assume "v = hd(stack e)"
      thus ?thesis
        using \<open>reachable v w\<close> by auto 
    next
      assume "v \<noteq> hd (stack e)"
      
  qed
qed

lemma pre_dfs_implies_post_dfs:
  fixes v e
  defines "e1 \<equiv> e\<lparr>visited := visited e \<union> {v}, stack := (v # stack e)\<rparr>"
  defines "e' \<equiv> dfss v (successors v) e1"
  assumes 1: "pre_dfs v e"
      and 2: "dfs_dfss_dom (Inl(v, e))"
      and 3: "post_dfss v (successors v) e'"
      and notempty: "v \<in> set (stack e')"
  shows "post_dfs v (dfs v e)"
proof (cases "v = hd(stack e')")
  case True
  with 2 have "dfs v e = e'\<lparr>sccs:=sccs e' \<union> {\<S> e' v}, 
                            explored:=explored e' \<union> (\<S> e' v), 
                            stack:=tl(stack e')\<rparr>" (is "_ = ?e2")
    unfolding e1_def e'_def by (simp add: dfs.psimps)
  moreover have "distinct (stack ?e2)"
    using 3 by (auto simp: post_dfss_def wf_env_def distinct_tl)

  moreover have "set (stack ?e2) \<subseteq> visited ?e2"
  proof -
    have "set (stack ?e2) = set (tl (stack e'))" by simp
    also have "\<dots> \<subseteq> visited e'"
      by (metis "3" list.set_sel(2) post_dfss_def subset_code(1) tl_Nil wf_env_def)
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
          by (metis "3" empty_iff graph.post_dfss_def graph_axioms wf_env_def)
      next
        case False
        have "w \<in> \<S> e' v"
          using False w1 by auto 
        have "w \<in> set(tl(stack e'))"
          using w2 by force
        hence "w \<noteq> v"
          by (metis "3" True distinct.simps(2) empty_iff empty_set list.collapse post_dfss_def tl_Nil wf_env_def) 
        hence "w \<in> \<S> e' w \<inter> \<S> e' v"
          using "3" \<open>w \<in> \<S> e' v\<close> post_dfss_def wf_env_def by fastforce
        thus ?thesis using 3 post_dfss_def wf_env_def
          by (metis (full_types) \<open>w \<in> set (tl (stack e'))\<close> \<open>w \<noteq> v\<close> emptyE list.set(1) list.set_sel(2) notempty) 
      qed
    }
    hence "set (tl (stack e')) \<inter> \<S> e' v = {}" by auto
    moreover have "stack ?e2 = tl(stack e')" by simp
    moreover have "explored ?e2 = explored e' \<union> \<S> e' v" by simp
    moreover have "explored e' \<inter> set (stack e') = {}"
      using 3 post_dfss_def wf_env_def graph_axioms by metis
    ultimately show ?thesis
      by (smt (verit, ccfv_threshold) Un_iff disjoint_iff empty_iff list.set(1) list.set_sel(2) notempty)
  qed

  moreover have "(\<forall>v w. w \<in> \<S> ?e2 v \<longleftrightarrow> (\<S> ?e2 v = \<S> ?e2 w))" sorry
  moreover have "(\<forall>v \<in> set (stack ?e2). \<forall> w \<in> set (stack ?e2). v \<noteq> w \<longrightarrow> \<S> ?e2 v \<inter> \<S> ?e2 w = {})" sorry
  moreover have"(\<forall> v. v \<notin> visited ?e2 \<longrightarrow> \<S> ?e2 v = {v})" sorry
  moreover have "\<Union> {\<S> ?e2 v | v . v \<in> set (stack ?e2)} = visited ?e2 - explored ?e2" sorry
  moreover have "\<forall> x. reachable v x \<longrightarrow> x \<in> explored ?e2" sorry

  ultimately show ?thesis sorry
next
  case False
  with 2 have "dfs v e = e'"
    unfolding e1_def e'_def by (simp add: dfs.psimps)
  hence "wf_env e'" using 3 post_dfss_def by metis
  have "\<forall> x. reachable v x \<longrightarrow> x \<in> visited e'"
    by (smt (verit, best) "3" graph.post_dfss_def graph.reachable.cases graph_axioms notempty subset_iff wf_env_def) 
  (* have "sub_env e e'"
  proof -
    have "visited e \<subseteq> visited e'" sorry
    have "explored e \<subseteq> explored e'" sorry
    have "\<forall> v. \<S> e v \<subseteq> \<S> e' v" sorry
  qed *)
  show ?thesis
    by (simp add: \<open>\<forall>x. reachable v x \<longrightarrow> x \<in> visited e'\<close> \<open>dfs v e = e'\<close> \<open>wf_env e'\<close> post_dfs_def) 
qed

lemma pre_dfss_implies_post_dfss:
  assumes "pre_dfss v vs e"
  shows "post_dfss v vs (dfss v vs e)"
    (is "post_dfss v vs ?e'")
  sorry



end
end