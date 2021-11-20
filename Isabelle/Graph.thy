theory Graph
imports Main
begin

declare Let_def[simp]

record 'v env =
  S :: "'v \<Rightarrow> 'v set"
  explored :: "'v set"
  visited :: "'v set"
  sccs :: "'v set set"
  stack :: "'v list"

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

function unite :: "'v \<Rightarrow> 'v \<Rightarrow> 'v env \<Rightarrow> 'v env" where
  "unite v w e =
      (if (S e v = S e w) then e
      else let r = hd(stack e);
               r'= hd(tl(stack e));
               joined = S e r \<union> S e r';
               e'= e \<lparr> stack := tl(stack e), S := (S e) (r := joined, r' := joined)\<rparr>
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
      then e'\<lparr>sccs:=sccs e' \<union> {S e v}, explored:=explored e' \<union> (S e v), stack:=tl(stack e')\<rparr>
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
  "
(*
Maybe add precedes (\<preceq>) def, cf L.543 - L.683 in Tarjan.thy
*)
(*
Definitions will help later in the proof in pre/post-conditions to ensure that all parameters are well-formed and fit the definitions.
It seems natural but Isabelle needs accurate details.
*)

text \<open>
  Precondition for function dfs.
\<close>
definition pre_dfs where "pre_dfs v e \<equiv> wf_env e \<and> v \<notin> visited e"
(*
Preconditions will appear in the proof like the following: a lemma assumes a predcond and shows a postcond.
*)
text \<open>
  Precondition for function dfss.
\<close>
definition pre_dfss where "pre_dfss v vs e \<equiv> wf_env e"

lemma pre_dfs_pre_dfss:
  assumes "pre_dfs v e"
  shows "pre_dfss v (successors v) (e \<lparr> visited := visited e \<union> {v}, stack := v # stack e\<rparr>)"
        (is "pre_dfss v ?succs ?e'")
(*  using assms unfolding pre_dfs_def pre_dfss_def wf_env_def by auto *)
proof -
  have "distinct (stack ?e')"
    sorry
  moreover have "set (stack ?e') \<subseteq> visited ?e'"
    sorry
  ultimately show ?thesis unfolding pre_dfss_def wf_env_def ..
qed


end
end