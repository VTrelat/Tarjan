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
     in (if w \<in> explored e
        then dfss v (vs-{w}) e
      else if w \<notin> visited e
        then dfs w e
      else unite v w e)))"
  by pat_completeness (force+)

(*
force : proves that dfs and dfss are functions. Method auto cannot terminate because of the mutual recursion.
The termination is not proved.
*)

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
  \<and> \<Union> {\<S> e v | v . v \<in> set (stack e)} = visited e - explored e
  "
(*
Maybe add precedes (\<preceq>) def, cf L.543 - L.683 in Tarjan.thy
*)
(*
Definitions will help later in the proof in pre/post-conditions to ensure that all parameters are well-formed and fit the definitions.
It seems natural but Isabelle needs accurate details.
*)

text \<open>
  Precondition and post-condition for function dfs.
\<close>
definition pre_dfs where "pre_dfs v e \<equiv> wf_env e \<and> v \<notin> visited e"
(*
Preconditions will appear in the proof like the following: a lemma assumes a predcond and shows a postcond.
*)

definition post_dfs where "post_dfs v e \<equiv> wf_env e"                                                                             

text \<open>
  Precondition for function dfss.
\<close>
definition pre_dfss where "pre_dfss v vs e \<equiv> wf_env e"

definition post_dfss where "post_dfss v vs e \<equiv> wf_env e"

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
       "(\<forall> v. v \<notin> visited ?e' \<longrightarrow> \<S> ?e' v = {v})"
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
  ultimately show ?thesis unfolding pre_dfss_def wf_env_def by blast
qed

lemma pre_dfss_pre_dfs:
  fixes w
  assumes "pre_dfss v vs e" and "w \<notin> visited e"
  shows "pre_dfs w e"
  using assms unfolding pre_dfss_def pre_dfs_def wf_env_def by auto


lemma pre_dfs_implies_post_dfs:
  fixes v e
  defines "e1 \<equiv> e\<lparr>visited := visited e \<union> {v}, stack := (v # stack e)\<rparr>"
  defines "e' \<equiv> dfss v (successors v) e1"
  assumes 1: "pre_dfs v e"
      and 2: "dfs_dfss_dom (Inl(v, e))"
      and 3: "post_dfss v (successors v) e'"
      (* and notempty: "stack e' \<noteq> []" *)
      and notempty "v \<in> set (stack e')"
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
      by (smt (verit, best) "3" assms(7) graph.post_dfss_def graph.wf_env_def graph_axioms singletonD subset_iff)
    ultimately show ?thesis by simp
  qed

  moreover have "explored ?e2 \<inter> set (stack ?e2) = {}"
  proof -
    have "explored e' \<inter> set(stack e') = {}"
      by (metis "3" post_dfss_def wf_env_def)
    moreover have "\<S> e' v \<inter> set (stack e') = {}"
    
  qed

  moreover have "(\<forall>v w. w \<in> \<S> ?e2 v \<longleftrightarrow> (\<S> ?e2 v = \<S> ?e2 w))" sorry
  moreover have "(\<forall>v \<in> set (stack ?e2). \<forall> w \<in> set (stack ?e2). v \<noteq> w \<longrightarrow> \<S> ?e2 v \<inter> \<S> ?e2 w = {})" sorry
  moreover have"(\<forall> v. v \<notin> visited ?e2 \<longrightarrow> \<S> ?e2 v = {v})" sorry
  moreover have "\<Union> {\<S> ?e2 v | v . v \<in> set (stack ?e2)} = visited ?e2 - explored ?e2" sorry

  ultimately show ?thesis unfolding post_dfs_def wf_env_def by auto 
next
  case False
  with 2 have "dfs v e = e'"
    unfolding e1_def e'_def by (simp add: dfs.psimps)
  with 3 show ?thesis
    unfolding post_dfs_def post_dfss_def by simp
qed

lemma pre_dfss_implies_post_dfss:
  assumes "pre_dfss v vs e"
  shows "post_dfss v vs (dfss v vs e)"
    (is "post_dfss v vs ?e'")
  sorry



end
end