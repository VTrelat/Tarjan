theory Graph
imports Main
begin

declare Let_def[simp]

text \<open>
  The following record is used to represent states
  during the execution of the algorithm computing
  strongly connected components.
\<close>
record 'v env =
  \<S> :: "'v \<Rightarrow> 'v set"
  explored :: "'v set"
  visited :: "'v set"
  sccs :: "'v set set"
  stack :: "'v list"


section \<open>Auxiliary lemmas on lists\<close>

text \<open>
  We use the precedence order on the elements that appear
  in a list. In particular, we represent the stack of
  the depth-first search algorithm as a list, and a
  node @{text x} precedes another node @{text y} on the
  stack of @{text y} was pushed on the stack earlier
  than @{text x}.
\<close>

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
  If a non-empty list @{text "zs"} is a suffix of @{text "xs"},
  both lists are repetition-free, and have the same head, then
  the two lists are equal.
\<close>
lemma suffix_same_head:
  assumes "xs = ys @ zs" and "distinct xs" and "zs \<noteq> []" and "hd xs = hd zs"
  shows "ys = []"
  using assms
  by (metis Nil_is_append_conv distinct.simps(2) in_set_conv_decomp list.exhaust_sel tl_append2)


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

text \<open>
  We inductively define reachability of nodes in the graph.
\<close>
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

text \<open>
  In order to derive a ``reverse'' induction rule for @{const "reachable"},
  we define an alternative reachability predicate and prove that the two
  coincide.
\<close>
inductive reachable_end where
  re_refl[iff]: "reachable_end x x"
| re_succ: "\<lbrakk>reachable_end x y; edge y z\<rbrakk> \<Longrightarrow> reachable_end x z"

lemma succ_re:
  assumes y: "edge x y" and z: "reachable_end y z"
  shows "reachable_end x z"
  using z y by (induction) (auto intro: re_succ)

lemma reachable_re:
  assumes "reachable x y"
  shows "reachable_end x y"
  using assms by (induction) (auto intro: succ_re)

lemma re_reachable:
  assumes "reachable_end x y"
  shows "reachable x y"
  using assms by (induction) (auto intro: succ_reachable)

lemma reachable_end_induct:
  assumes r: "reachable x y"
      and base: "\<And>x. P x x"
      and step: "\<And>x y z. \<lbrakk>P x y; edge y z\<rbrakk> \<Longrightarrow> P x z"
  shows "P x y"
using r[THEN reachable_re] proof (induction)
  case (re_refl x)
  from base show ?case .
next
  case (re_succ x y z)
  with step show ?case by blast
qed

text \<open>
  We also need the following variant of reachability avoiding
  some node. More precisely, @{text y} is reachable from @{text x}
  avoiding @{text S} if there exists a path such that no node from
  @{text S} appears along the path, except possibly as the start
  node.
\<close>
inductive reachable_avoiding where
  ra_refl[iff]: "reachable_avoiding x x S"
| ra_succ[elim]: "\<lbrakk>reachable_avoiding x y S; edge y z; z \<notin> S\<rbrakk> \<Longrightarrow> reachable_avoiding x z S"

lemma edge_ra:
  assumes "edge x y" and "y \<notin> S"
  shows "reachable_avoiding x y S"
  using assms by (meson reachable_avoiding.simps)

lemma ra_trans:
  assumes 1: "reachable_avoiding x y S" and 2: "reachable_avoiding y z S"
  shows "reachable_avoiding x z S"
  using 2 1 by induction auto

lemma ra_cases:
  assumes "reachable_avoiding x y S"
  shows "x=y \<or> (\<exists>z. z \<in> successors x - {x} \<and> z \<notin> S \<and> reachable_avoiding z y S)"
using assms proof (induction)
  case (ra_refl x S)
  then show ?case by simp
next
  case (ra_succ x y S z)
  then show ?case
    by (metis DiffI emptyE insert_iff ra_refl reachable_avoiding.ra_succ)
qed

lemma ra_mono: 
  assumes "reachable_avoiding x y S" and "S' \<subseteq> S"
  shows "reachable_avoiding x y S'"
using assms by induction auto

text \<open>
  Reachability avoiding some nodes obviously implies reachability.
  Conversely, if @{text y} is reachable from @{text "x \<in> S"} then there
  exists some @{text "x' \<in> S"} from which @{text y} can be reached
  without (again) passing through @{text S}.
\<close>
lemma ra_reachable:
  "reachable_avoiding x y S \<Longrightarrow> reachable x y"
  by (induction rule: reachable_avoiding.induct) (auto intro: succ_reachable)

lemma reach_avoid:
  assumes r: "reachable x y" and x: "x \<in> S"
  shows "\<exists>x'\<in>S. reachable_avoiding x' y S"
  using r[THEN reachable_re] x proof (induction)
  case (re_refl x)
  then show ?case by auto
next
  case (re_succ x y z)
  show ?case 
  proof (cases "z \<in> S")
    case True
    then show ?thesis by auto
  next
    case False
    with re_succ ra_succ show ?thesis by blast
  qed
qed


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

(*
function unite :: "'v \<Rightarrow> 'v \<Rightarrow> 'v env \<Rightarrow> 'v env" where
  "unite v w e =
      (if (\<S> e v = \<S> e w) then e
      else let r = hd(stack e);
               r'= hd(tl(stack e));
               joined = \<S> e r \<union> \<S> e r';
               e'= e \<lparr> stack := tl(stack e), \<S> := (\<lambda>n. if n \<in> joined then joined else \<S> e n) \<rparr>
          in unite v w e')"
  by pat_completeness auto
*)

definition unite :: "'v \<Rightarrow> 'v \<Rightarrow> 'v env \<Rightarrow> 'v env" where
  "unite v w e \<equiv>
     let pfx = takeWhile (\<lambda>x. w \<notin> \<S> e x) (stack e);
         sfx = dropWhile (\<lambda>x. w \<notin> \<S> e x) (stack e);
         cc = \<Union> { \<S> e x | x . x \<in> set pfx \<union> {hd sfx} }
     in  e\<lparr>\<S> := \<lambda>x. if x \<in> cc then cc else \<S> e x,
           stack := sfx\<rparr>"

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
definition pre_dfs where 
  "pre_dfs v e \<equiv> 
     wf_env e
   \<and> v \<notin> visited e
   \<and> (\<forall> n \<in> set (stack e). reachable n v)"

definition post_dfs where 
  "post_dfs v prev_e e \<equiv> 
     wf_env e
   \<and> (\<forall> x. reachable v x \<longrightarrow> x \<in> visited e)
   \<and> sub_env prev_e e
   \<and> (\<forall> n \<in> set (stack e). reachable n v)
   \<and> (\<exists> ns. stack prev_e = ns @ (stack e))
   \<and> ((v \<in> explored e \<and> stack e = stack prev_e \<and> (\<forall>n \<in> set (stack e). \<S> e n = \<S> prev_e n)) 
       \<or> (stack e \<noteq> [] \<and> v \<in> \<S> e (hd (stack e)) 
          \<and> (\<forall>n \<in> set (tl (stack e)). \<S> e n = \<S> prev_e n))
          \<and> (\<forall>n \<in> set (tl (stack e)). \<forall>w \<in> \<S> e (hd (stack e)) - \<S> prev_e (hd (stack e)).
                \<not> reachable_avoiding w n (\<S> e (hd (stack e)))))
"
(*
   \<and> ((v \<in> explored e \<and> stack e = stack prev_e)
       \<or> (v \<in> \<S> e (hd (stack e)) \<and> (\<exists> n \<in> set (stack prev_e). \<S> e v = \<S> e n)))"
*)
(* \<and> (\<forall> m n. m \<preceq> n in (stack prev_e) \<longrightarrow> (\<forall> u \<in> \<S> prev_e m. reachable u v \<and> reachable v n \<longrightarrow> \<S> e m = \<S> e n)) *) (* wrong *)
(* \<and> (\<forall> n \<in> set (stack e). reachable v n \<longrightarrow> v \<in> \<S> e n) *)
(* \<and> (\<forall> x. reachable v x \<longrightarrow> x \<in> explored e)" *) (* wrong *)

text \<open>
  Precondition for function dfss.
\<close>
definition pre_dfss where 
  "pre_dfss v vs e \<equiv> 
     wf_env e 
   \<and> v \<in> visited e
   \<and> vs \<subseteq> successors v
   \<and> (\<forall>w \<in> successors v - vs. w \<in> explored e \<union> \<S> e (hd (stack e)))
   \<and> (\<forall> n \<in> set (stack e). reachable n v)
   \<and> (stack e \<noteq> [])
   \<and> (v \<in> \<S> e (hd (stack e)))
   \<and> (hd (stack e) = v \<longrightarrow>
         (\<forall>n \<in> set (tl (stack e)). \<forall>w \<in> \<S> e (hd (stack e)) - {v}.
             \<not> reachable_avoiding w n (\<S> e (hd (stack e)))))
"
(* \<and> (\<forall>n \<in> set (stack e). \<forall>w \<in> successors v - vs. reachable w n \<longrightarrow> w \<in> \<S> e v) *)
(* \<and> (\<forall> n \<in> set (stack e). reachable v n \<longrightarrow> v \<in> \<S> e n \<or> (\<exists> m \<in> vs. reachable m n)) *) (* wrong *)
(*   \<and> (\<forall>n \<in> set (tl (stack e)). \<forall>w \<in> successors v - vs.
         \<not> reachable_avoiding w n (\<S> e (hd (stack e)))) *)

definition post_dfss where 
  "post_dfss v vs prev_e e \<equiv> 
     wf_env e
   \<and> (\<forall> w \<in> vs. \<forall> x. reachable w x \<longrightarrow> x \<in> visited e)
   \<and> sub_env prev_e e
   \<and> (\<forall>w \<in> successors v. w \<in> explored e \<union> \<S> e (hd (stack e)))
   \<and> (\<forall> n \<in> set (stack e). reachable n v)
   \<and> (stack e \<noteq> [])
   \<and> (\<exists> ns. stack prev_e = ns @ (stack e))
   \<and> (v \<in> \<S> e (hd (stack e)))
   \<and> (\<forall>n \<in> set (tl (stack e)). \<S> e n = \<S> prev_e n)
   \<and> (hd (stack e) = v \<longrightarrow>
         (\<forall>n \<in> set (tl (stack e)). \<forall>w \<in> \<S> e (hd (stack e)) - {v}.
             \<not> reachable_avoiding w n (\<S> e (hd (stack e)))))
   \<and> (hd (stack e) = v \<longrightarrow> (\<forall>n \<in> set (tl (stack e)). \<not> reachable v n)) 
"
(* \<and> (set (stack e) \<subseteq> set (stack prev_e) \<union> {v})" *) 
(* \<and> (\<forall> w \<in> vs. \<forall> x. reachable w x \<longrightarrow> x \<in> explored e)" *) (* false *)
(* \<and> (\<forall> n \<in> set (stack e). reachable v n \<longrightarrow> v \<in> \<S> e n) *) (* wrong *)
(* \<and> (\<forall>n \<in> set (tl (stack e)). \<not> reachable_avoiding v n (\<S> e (hd (stack e)))) *)


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
              using assms by (auto simp: pre_dfs_def wf_env_def)
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
        using assms by (simp add: pre_dfs_def wf_env_def)
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

  moreover
  have subsucc:"v \<in> visited ?e'" by simp

  moreover
  have reachstack:"\<forall> n \<in> set (stack ?e'). reachable n v"
    by (simp add: \<open>\<forall>x y. x \<preceq> y in stack ?e' \<longrightarrow> reachable y x\<close> head_precedes)

  moreover
  have notempty: "stack ?e' \<noteq> []"
    by simp

  moreover
  have "v \<in> \<S> ?e' (hd (stack ?e'))"
    using "1"(5) by auto

  moreover
  from \<open>pre_dfs v e\<close> have "\<S> ?e' (hd (stack ?e')) = {v}"
    by (simp add: pre_dfs_def wf_env_def)

  ultimately show ?thesis
    unfolding pre_dfss_def by simp
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
  with 3 have "stack e' = v # tl(stack e')"
    by (auto simp: post_dfss_def)
  hence notempty: "v \<in> set (stack e')"
    by (metis list.set_intros(1))
  with 2 have e2:"dfs v e = e'\<lparr>sccs:=sccs e' \<union> {\<S> e' v}, 
                            explored:=explored e' \<union> (\<S> e' v), 
                            stack:=tl(stack e')\<rparr>" (is "_ = ?e2")
    unfolding e1_def e'_def
    using True assms(1) assms(2) dfs.psimps by force
  have stack:"stack ?e2 = tl (stack e')" by simp
  have Se'e2_eq:"\<forall> x. \<S> e' x = \<S> ?e2 x"
    by simp
  have sub:"sub_env e e1" unfolding sub_env_def
    using e1_def by auto
  have stacke1:"stack e' = stack e1"
  proof -
    obtain ns where ns_def:"stack e1 = ns @ (stack e')" using 3 unfolding post_dfss_def
      by blast
    have "ns = []"
    proof (rule ccontr)
      assume "ns \<noteq> []"
      hence "hd(ns) = v" using e1_def ns_def
        by (metis hd_append2 list.sel(1) select_convs(5) surjective update_convs(5))
      hence "\<not> distinct (stack e1)" using True ns_def \<open>ns \<noteq> []\<close>
        by (metis disjoint_iff_not_equal distinct_append hd_in_set notempty) 
      then show False using e1_def
        by (smt (verit, ccfv_threshold) "1" distinct.simps(2) in_mono pre_dfs_def select_convs(5) surjective update_convs(3) update_convs(5) wf_env_def)
    qed
    then show ?thesis using 3 True wf_env_def
      by (simp add: ns_def)
  qed
  moreover have subenv:"sub_env e ?e2" 
  proof -
    from 3 sub have e:"visited e \<subseteq> visited e'"
      by (auto simp: post_dfss_def sub_env_def)
    have e':"visited e' \<subseteq> visited ?e2" unfolding e'_def
      by (simp add: dfs.psimps)
    from e and e' have visited:"visited e \<subseteq> visited ?e2"
      by blast

    from 3 sub have e:"explored e \<subseteq> explored e'"
      by (auto simp: post_dfss_def sub_env_def)
    have e':"explored e' \<subseteq> explored ?e2" unfolding e'_def
      by (simp add: dfs.psimps)
    from e and e' have explored:"explored e \<subseteq> explored ?e2"
      by blast

    have S:"\<forall> v. \<S> e v \<subseteq> \<S> ?e2 v"
    proof -
      from 3 sub have e:"\<forall> v. \<S> e v \<subseteq> \<S> e' v"
        unfolding post_dfss_def sub_env_def by fast
      have e':"\<forall> v. \<S> e' v \<subseteq> \<S> ?e2 v"
        by (simp add: dfs.psimps)
      from e and e' have "\<forall> v. \<S> e v \<subseteq> \<S> ?e2 v"
        by blast
      thus ?thesis by simp
    qed

    have union:"\<Union> {\<S> e n | n. n \<in> set (stack e)} \<subseteq> \<Union> {\<S> ?e2 n | n. n \<in> set (stack ?e2)}"
    proof -
      have "stack ?e2 = tl(stack e')"
        using stack by blast
      then have "... = stack e" using True
        by (metis \<open>stack e' = v # tl (stack e')\<close> calculation e1_def list.inject select_convs(5) surjective update_convs(5))
      hence incl:"\<Union> {\<S> ?e2 n | n. n \<in> set (stack ?e2)} = \<Union> {\<S> e' n | n. n \<in> set (stack e)}" using Se'e2_eq
        by force
      have "sub_env e1 e'"
        using 3 post_dfss_def by auto
      hence "sub_env e e'" using sub
        by (meson order.trans sub_env_def)
      {
        fix n
        assume "n \<in> \<Union> {\<S> e n | n. n \<in> set (stack e)}"
        then obtain x where x_def:"n \<in> \<S> e x \<and> x \<in> set(stack e)"
          by blast 
        from \<open>sub_env e e'\<close> have "\<S> e x \<subseteq> \<S> e' x"
          by (simp add: sub_env_def)
        hence "n \<in> \<S> e' x"
          using x_def by blast
        hence "n \<in> \<Union> {\<S> e' n | n. n \<in> set (stack e)}"
          using x_def by blast
      }
      then show ?thesis
        using incl by fastforce
    qed

    from visited explored S union show ?thesis
      using sub_env_def by blast
  qed

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
          with 3 show ?thesis
            by (auto simp: post_dfss_def wf_env_def)
        next
          case False
          with 1 show ?thesis
            by (auto simp: pre_dfs_def wf_env_def)
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
      with 3 have reachable:"\<forall> x y. x \<preceq> y in stack e' \<longrightarrow> reachable y x"
        by (auto simp: post_dfss_def wf_env_def)
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
        show ?thesis
        proof (cases "y \<in> explored e'")
          case True
          then show ?thesis
            by simp
        next
          case False
          from False visitedy have "y \<in> \<Union> {\<S> e' v | v. v \<in> set (stack e')}" using wf_env_def[of e'] assms(5)
            by (simp add: post_dfss_def)
          then obtain n where ndef: "n \<in> set (stack e') \<and> (y \<in> \<S> e' n)"
            by force
          show ?thesis
          proof (cases "n = v")
            case True
            with ndef show ?thesis by simp
          next
            case False
            with ndef \<open>stack e' = v # tl(stack e')\<close>
            have "n \<in> set (tl (stack e'))"
              by (metis set_ConsD)
            moreover
            from 3 have "is_subscc (\<S> e' n)" "n \<in> \<S> e' n"
              unfolding post_dfss_def wf_env_def by auto
            with ndef have "reachable y n"
              by (auto simp: is_subscc_def)
            hence "reachable v n"
              using \<open>reachable v y\<close> reachable_trans by blast
            ultimately show ?thesis
              using \<open>v = hd (stack e')\<close> 3 by (simp add: post_dfss_def)
          qed
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
            with 3 xv \<open>stack e' = v # tl(stack e')\<close> show ?thesis
              by (smt (verit) list.sel(1) post_dfss_def set_ConsD)
          next
            case False
            have "x \<in> explored e'"
              using True \<open>x \<in> S' \<and> x \<notin> S\<close> calculation(11) calculation(5) xv by auto
            from assms(5) have "\<forall> x \<in> explored e'. \<forall> y. reachable x y \<longrightarrow> y \<in> explored e'" using post_dfss_def unfolding wf_env_def
              by (simp add: post_dfss_def wf_env_def)
            hence "v \<in> explored e'" using False
              using \<open>x \<in> explored e'\<close> xv by blast
            with 3 notempty show ?thesis
              unfolding post_dfss_def wf_env_def by auto
          qed
          then have "is_scc S"
            using Se'e2_eq True \<open>x \<in> S' \<and> x \<notin> S\<close> calculation(5) by blast
        }
        then show ?thesis
          by blast
      next
        case False
        with asm 3 show ?thesis
          by (auto simp: post_dfss_def wf_env_def)
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

  moreover have stack_reachable:"\<forall> n \<in> set (stack ?e2). reachable n v" 
    using assms stack unfolding post_dfss_def
    by (metis list.set_sel(2))

  moreover have "\<exists> ns. stack e = ns @ (stack ?e2)"
  proof -
    have "stack ?e2 = tl(stack e')"
      using stack by blast
    then have "... = stack e" using True
      by (metis \<open>stack e' = v # tl (stack e')\<close> calculation(1) e1_def list.inject select_convs(5) surjective update_convs(5))
    thus ?thesis
      by simp
  qed


  moreover have stack:"stack ?e2 = tl(stack e')" by simp
  with True stack have stacke':"set (stack e') = set (stack ?e2)  \<union> {v}"
    by (metis Un_insert_right empty_iff empty_set list.exhaust_sel list.simps(15) notempty sup_bot.right_neutral)

  moreover 
  from stacke1 stack stacke' have "stack ?e2 = stack e"
    by (auto simp: e1_def)

  moreover
  from 3 True have "v \<in> explored ?e2"
    by (auto simp: post_dfss_def)
  
  moreover
  from 3 have "\<forall>n \<in> set (stack ?e2). \<S> ?e2 n = \<S> e n"
    by (auto simp: post_dfss_def e1_def)

  ultimately show ?thesis
    unfolding post_dfs_def using e2 by simp
next
  case False
  with 2 have e':"dfs v e = e'"
    unfolding e1_def e'_def by (simp add: dfs.psimps)

  moreover from 3 have wfenv:"wf_env e'" 
    by (simp add: post_dfss_def)

  moreover have subenv:"sub_env e e'"
  proof -
    have "sub_env e e1"
      unfolding sub_env_def
      by (auto simp: e1_def)
    with 3 show ?thesis
      unfolding post_dfss_def sub_env_def 
      by (meson subset_trans)
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
      with 3 show ?thesis
        by (auto simp: post_dfss_def)
    qed
  
  qed

  moreover have stack_visited: "\<forall> n \<in> set (stack e'). reachable n v"
    using 3 by (auto simp: post_dfss_def)

  moreover have "\<exists> ns. stack e = ns @ (stack e')"
  proof -
    from 3 obtain ns where "stack e1 = ns @ stack e'"
      unfolding post_dfss_def by blast
    moreover have "... = v # stack e" using e1_def
      using calculation by simp
    moreover have "ns \<noteq> []" using False
      using calculation by auto
    moreover have "stack e = tl(ns) @ stack e'"
      by (metis calculation(2) calculation(3) list.sel(3) tl_append2)
    ultimately show ?thesis
      by blast
  qed

  moreover
  have "stack e' \<noteq> []" "v \<in> \<S> e' (hd (stack e'))"
       "\<forall>n \<in> set (tl (stack e')). \<S> e' n = \<S> e n"
    using 3 by (auto simp: post_dfss_def e1_def)

  moreover
  have "(\<forall>n \<in> set (tl (stack e')). \<forall>w \<in> \<S> e' (hd (stack e')) - \<S> e (hd (stack e')).
               \<not> reachable_avoiding w n (\<S> e' (hd (stack e'))))"
    sorry
(*
  proof (clarify)
    fix n w
    assume asm: "v = hd (stack e')" 
                "n \<in> set (tl (stack e'))" "w \<in> \<S> e' (hd (stack e'))"
                "reachable_avoiding w n (\<S> e' (hd (stack e')))"
    show "False"
    proof (cases "w = v")
      case True
      with \<open>stack e' \<noteq> []\<close> \<open>v \<in> \<S> e' (hd (stack e'))\<close> 
           \<open>n \<in> set (tl (stack e'))\<close> \<open>wf_env e'\<close>
      have "v \<noteq> n" 
        unfolding wf_env_def
        by (metis (no_types, lifting) Diff_cancel Diff_triv False empty_iff list.set_sel)
      with True asm obtain w' where
        w': "w' \<in> successors v - {v}" "reachable_avoiding w' n (\<S> e' (hd (stack e')))"
        using ra_cases by blast
      show ?thesis
      proof (cases "w' \<in> explored e'")
        case True
        with ra_reachable[OF \<open>reachable_avoiding w' n (\<S> e' (hd (stack e')))\<close>]
             \<open>stack e' \<noteq> []\<close> \<open>n \<in> set (tl (stack e'))\<close> \<open>wf_env e'\<close>
        show ?thesis unfolding wf_env_def by (meson disjoint_iff list.set_sel(2))
      next
        case False
        with 3 \<open>v = hd (stack e')\<close> 
             \<open>w' \<in> successors v - {v}\<close> \<open>n \<in> set (tl (stack e'))\<close>
             \<open>reachable_avoiding w' n (\<S> e' (hd (stack e')))\<close>
        show ?thesis
          by (auto simp: post_dfss_def)
      qed
    next
      case False
      with 3 asm show ?thesis 
        by (auto simp: post_dfss_def)
    qed
  qed
*)
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
  then show "post_dfs v e (dfs v e)"
    using pre_dfs_implies_post_dfs pre_dfs_pre_dfss by auto
next
  fix v vs e
  assume dom:"dfs_dfss_dom (Inr(v,vs,e))"
     and predfss:"pre_dfss v vs e"
     and prepostdfs:"\<And>w. \<lbrakk> vs \<noteq> {}; w = (SOME x. x \<in> vs); w \<notin> explored e; w \<notin> visited e; pre_dfs w e \<rbrakk> \<Longrightarrow> post_dfs w e (dfs w e)"
     and prepostdfss:"\<And>w e'. \<lbrakk> vs \<noteq> {}; w = (SOME x. x \<in> vs); e' = (if w \<in> explored e then e else if w \<notin> visited e then dfs w e else unite v w e);pre_dfss v (vs - {w}) e' \<rbrakk> \<Longrightarrow> post_dfss v (vs - {w}) e' (dfss v (vs - {w}) e')"
  show "post_dfss v vs e (dfss v vs e)"
  proof (cases "vs = {}")
    case True
    hence return_e:"dfss v vs e = e" using dom dfss.psimps by metis
    moreover have "wf_env e"
      using predfss by (simp add: pre_dfss_def)
    moreover have "\<forall>w \<in> vs. \<forall>x. reachable w x \<longrightarrow> x \<in> visited e"
      by (simp add: True)
    moreover have "sub_env e e"
      by (simp add: sub_env_def)
    moreover have "\<forall>w \<in> successors v. w \<in> explored e \<union> \<S> e (hd (stack e))"
      using predfss True by (simp add: pre_dfss_def)
    moreover have "\<forall> n \<in> set (stack e). reachable n v"
      using pre_dfss_def predfss by blast
    moreover have "stack e \<noteq> []"
      using pre_dfss_def predfss by blast
    moreover have "\<exists> ns. stack e = ns @ (stack e)"
      by simp
    moreover have "v \<in> \<S> e (hd (stack e))"
      using pre_dfss_def predfss by blast
    moreover
    have "hd (stack e) = v \<longrightarrow>
             (\<forall>n \<in> set (tl (stack e)). \<forall>w \<in> \<S> e (hd (stack e)) - {v}.
                 \<not> reachable_avoiding w n (\<S> e (hd (stack e))))"
      using predfss by (auto simp: pre_dfss_def)
    moreover
    {
      fix n
      assume asm: "hd (stack e) = v"
                  "n \<in> set (tl (stack e))"
                  "reachable v n"
      from \<open>v \<in> \<S> e (hd (stack e))\<close> \<open>reachable v n\<close>
      obtain w where "w \<in> \<S> e (hd (stack e))" "reachable_avoiding w n (\<S> e (hd (stack e)))"
        using reach_avoid by blast
      with predfss \<open>hd (stack e) = v\<close> \<open>n \<in> set (tl (stack e))\<close> have "w = v"
        by (auto simp: pre_dfss_def)
      from asm \<open>stack e \<noteq> []\<close> \<open>wf_env e\<close> have "v \<noteq> n"
        unfolding wf_env_def by (metis distinct.simps(2) hd_Cons_tl)
      with ra_cases[OF \<open>reachable_avoiding w n (\<S> e (hd (stack e)))\<close>] \<open>w = v\<close> 
      obtain w' where
        w': "w' \<in> successors v" "w' \<notin> \<S> e (hd (stack e))"
            "reachable_avoiding w' n (\<S> e (hd (stack e)))"
        by blast
      with predfss \<open>vs = {}\<close> have "w' \<in> explored e"
        by (auto simp: pre_dfss_def)
      with ra_reachable[OF \<open>reachable_avoiding w' n (\<S> e (hd (stack e)))\<close>]
           \<open>n \<in> set (tl (stack e))\<close> \<open>stack e \<noteq> []\<close> \<open>wf_env e\<close>
      have "False"
        unfolding wf_env_def by (metis Int_iff empty_iff list.set_sel(2))
    }
    ultimately show ?thesis
      by (force simp: post_dfss_def)
  next
    case vs_case: False
    define w where "w = (SOME x. x \<in> vs)"
    define e' where "e' = (if w \<in> explored e then e else if w \<notin> visited e then dfs w e else unite v w e)"
    from vs_case have wvs: "w \<in> vs"
      unfolding w_def by (simp add: some_in_eq)
    show ?thesis
    proof (cases "w \<in> explored e")
      case True
      hence dfss: "dfss v vs e = dfss v (vs - {w}) e'"
        by (simp add: dom vs_case w_def dfss.psimps e'_def)

      from True have env_eq: "e' = e" by (simp add: e'_def)
(*
      with predfss True have "pre_dfss v (vs - {w}) e'"
        by (auto simp: pre_dfss_def wf_env_def) -- works, very slow 
*)
      have "pre_dfss v (vs - {w}) e'"
      proof -
        from predfss env_eq have "pre_dfss v vs e'"
          by simp
        hence "wf_env e'" 
              "v \<in> visited e'" 
              "vs - {w} \<subseteq> successors v"
              "\<forall>n \<in> set (stack e'). reachable n v"
              "stack e' \<noteq> []"
              "v \<in> \<S> e' (hd (stack e'))"
              "hd (stack e') = v \<longrightarrow>
                  (\<forall>n \<in> set (tl (stack e')). \<forall>w \<in> \<S> e' (hd (stack e')) - {v}.
                      \<not> reachable_avoiding w n (\<S> e' (hd (stack e'))))"
          by (auto simp: pre_dfss_def)
        moreover
        {
          fix u
          assume u: "u \<in> successors v - (vs - {w})"
          have "u \<in> explored e' \<union> \<S> e' (hd (stack e'))"
          proof (cases "u = w")
            case True
            with \<open>w \<in> explored e\<close> show ?thesis
              by (simp add: env_eq)
          next
            case False
            with u predfss show ?thesis
              by (simp add: pre_dfss_def env_eq)
          qed
        }
        ultimately show ?thesis
          by (auto simp: pre_dfss_def)
      qed

      then have post: "post_dfss v (vs - {w}) e' (dfss v (vs - {w}) e')"
        using True \<open>e' = e\<close> prepostdfss vs_case w_def by auto

      moreover have wfenv: "wf_env (dfss v vs e)"
        using dfss post by (auto simp: post_dfss_def)
      moreover have reach:"\<forall> u \<in> vs. \<forall> x. reachable u x \<longrightarrow> x \<in> visited (dfss v vs e)"
      proof (clarify)
        fix u x
        assume asm:"u \<in> vs" "reachable u x"
        show "x \<in> visited (dfss v vs e)"
        proof (cases "u = w")
          case True
          with \<open>w \<in> explored e\<close> \<open>e' = e\<close> asm wfenv dfss post
          show ?thesis unfolding wf_env_def post_dfss_def sub_env_def
            by (metis subset_eq)
        next
          case False
          with asm post dfss \<open>e' = e\<close> show ?thesis
            by (auto simp: post_dfss_def)
        qed
      qed

      ultimately show ?thesis
        by (simp add: env_eq dfss post_dfss_def)
    next
      case notexplored: False
      then show ?thesis
      proof (cases "w \<notin> visited e")
        case True
        hence "e' = dfs w e" using e'_def notexplored
          by auto
        hence postdfsw: "post_dfs w e e'"
          using True notexplored pre_dfss_pre_dfs predfss prepostdfs some_in_eq vs_case w_def by blast
        moreover have "dfss v vs e = dfss v (vs - {w}) e'"
          using True dfss.psimps dom e'_def notexplored vs_case w_def by force
        moreover have "pre_dfss v (vs - {w}) e'"
        proof -
          from postdfsw have "wf_env e'"
            using post_dfs_def by blast
          moreover have "v \<in> visited e'"
            by (metis graph.post_dfs_def graph_axioms in_mono postdfsw pre_dfss_def predfss sub_env_def)
          moreover have "vs - {w} \<subseteq> successors v"
            by (metis Diff_subset pre_dfss_def predfss subset_trans)
          
          moreover have "\<forall> n \<in> set (stack e'). reachable n v" 
            using postdfsw post_dfs_def
            by (metis Un_iff pre_dfss_def predfss set_append)

          moreover have "stack e' \<noteq> []"
          proof -
            have "v \<notin> explored e"
            proof (rule ccontr)
              assume contrad:"\<not> v \<notin> explored e"
              have "w \<in> vs" using w_def
                using some_in_eq vs_case by blast
              then show False using notexplored wf_env_def predfss pre_dfss_def contrad
                by (smt (verit, best) in_mono reachable_edge)
            qed

            moreover have "v \<in> visited e"
              using pre_dfss_def predfss by blast
            
            ultimately show ?thesis
            proof -
              have "v \<in> visited e - explored e"
                by (simp add: \<open>v \<in> visited e\<close> \<open>v \<notin> explored e\<close>)
              hence "v \<in> \<Union> {\<S> e v | v. v \<in> set (stack e)}" using predfss wf_env_def unfolding wf_env_def
                by (simp add: pre_dfss_def wf_env_def)
              then obtain u where u_def:"u \<in> set (stack e)" "v \<in> \<S> e u" using pre_dfss_def predfss wf_env_def 
                by blast
              from predfss have "u \<in> \<S> e u"
                by (auto simp: pre_dfss_def wf_env_def)
              hence "u \<in> \<Union>{\<S> e n | n. n \<in> set (stack e)}" using u_def(1)
                by blast
              moreover have "sub_env e e'"
                using post_dfs_def postdfsw by blast
              hence "u \<in> \<Union>{\<S> e' n | n. n \<in> set (stack e')}" using calculation unfolding sub_env_def
                by blast
              thus ?thesis
                by force
            qed
          qed

          moreover have "\<exists> ns. stack e = ns @ (stack e')"
            using post_dfs_def postdfsw by blast

          moreover
          {
            fix u
            assume u: "u \<in> successors v - (vs - {w})"
            have "u \<in> explored e' \<union> \<S> e' (hd (stack e'))"
            proof (cases "u = w")
              case True
              with postdfsw show ?thesis
                by (auto simp: post_dfs_def)
            next
              case False
              with predfss u have "u \<in> explored e \<union> \<S> e (hd (stack e))"
                by (auto simp: pre_dfss_def)
              then show ?thesis
              proof
                assume "u \<in> explored e"
                with postdfsw show ?thesis
                  by (auto simp: post_dfs_def sub_env_def)
              next
                assume u: "u \<in> \<S> e (hd (stack e))"
                from predfss have "stack e \<noteq> []"
                  by (simp add: pre_dfss_def)
                with u have "u \<in> \<Union> {\<S> e n | n . n \<in> set (stack e)}"
                  by force
                moreover
                from postdfsw have "sub_env e e'"
                  by (simp add: post_dfs_def)
                ultimately obtain n where
                  n: "n \<in> set (stack e')" "u \<in> \<S> e' n"
                  using u unfolding sub_env_def by blast
                have "n = hd (stack e')"
                proof (rule ccontr)
                  assume "n \<noteq> hd (stack e')"
                  with postdfsw n \<open>stack e' \<noteq> []\<close> 
                  have "\<S> e' n = \<S> e n"
                    unfolding post_dfs_def by (metis hd_Cons_tl set_ConsD)
                  moreover
                  from n \<open>n \<noteq> hd (stack e')\<close> \<open>stack e' \<noteq> []\<close>
                       \<open>\<exists>ns. stack e = ns @ (stack e')\<close>
                  have "n \<in> set (tl (stack e))"
                    by (metis Un_iff append_Nil hd_Cons_tl set_ConsD set_append tl_append2)
                  ultimately show "False"
                    using u n \<open>stack e \<noteq> []\<close> predfss
                    unfolding pre_dfss_def wf_env_def
                    by (metis (no_types, opaque_lifting) Diff_cancel Diff_triv distinct.simps(2) empty_iff list.exhaust_sel list.set_sel(1) list.set_sel(2))
                qed
                with n show ?thesis by simp
              qed
            qed
          }

          moreover have "v \<in> \<S> e' (hd (stack e'))"
          proof (cases "stack e' = stack e")
            case True
            then show ?thesis
              by (metis post_dfs_def postdfsw pre_dfss_def predfss sub_env_def subset_iff)
          next
            case False
            with postdfsw have se': "w \<in> \<S> e' (hd (stack e'))" "\<forall>n \<in> set (tl (stack e')). \<S> e' n = \<S> e n"
              by (auto simp: post_dfs_def)
            from predfss have "hd (stack e) \<in> set (stack e)" "v \<in> \<S> e (hd (stack e))"
              by (auto simp: pre_dfss_def)
            with postdfsw obtain n where
              n: "n \<in> set (stack e')" "v \<in> \<S> e' n"
              unfolding post_dfs_def sub_env_def by blast
            show ?thesis
            proof (cases "n = hd (stack e')")
              case True
              with n show ?thesis by simp
            next
              case False
              with \<open>stack e' \<noteq> []\<close> n have "n \<in> set (tl (stack e'))"
                by (metis hd_Cons_tl set_ConsD)
              with se' n have "v \<in> \<S> e n"
                by blast
              from \<open>n \<in> set (tl (stack e'))\<close> postdfsw \<open>stack e' \<noteq> []\<close> n 
              have "n \<in> set (tl (stack e))"
                unfolding post_dfs_def
                by (metis precedes_append_left precedes_refl self_append_conv2 tl_append2)
              from predfss have "wf_env e" "stack e \<noteq> []" "v \<in> \<S> e (hd (stack e))"
                by (auto simp: pre_dfss_def)
              with \<open>n \<in> set (tl (stack e))\<close> \<open>v \<in> \<S> e n\<close> show ?thesis
                unfolding wf_env_def
                by (smt (verit, best) IntI Int_Diff Int_subset_iff UnionI distinct.simps(2) empty_iff empty_subsetI equalityD2 equalityI list.exhaust_sel list.set_sel(1) list.set_sel(2) mem_Collect_eq)
            qed
          qed

          moreover
          {
            fix n u
            assume asm: "hd (stack e') = v"
                        "n \<in> set (tl (stack e'))" "u \<in> \<S> e' (hd (stack e')) - {v}"
                        "reachable_avoiding u n (\<S> e' (hd (stack e')))"
            from postdfsw obtain ns where "stack e = ns @ (stack e')"
              unfolding post_dfs_def by blast
            with \<open>stack e' \<noteq> []\<close> \<open>hd (stack e') = v\<close> predfss
            have "hd (stack e) = v"
              unfolding pre_dfss_def wf_env_def
              by (smt (z3) Un_iff disjoint_iff list.set_sel(1) set_append)
            with \<open>stack e = ns @ (stack e')\<close> \<open>hd (stack e') = v\<close> \<open>stack e' \<noteq> []\<close> predfss
            have "stack e' = stack e" 
              unfolding pre_dfss_def wf_env_def
              by (metis self_append_conv2 suffix_same_head)
            have "False"
            proof (cases "u \<in> \<S> e (hd (stack e'))")
              case True
              from \<open>reachable_avoiding u n (\<S> e' (hd (stack e')))\<close> postdfsw
              have "reachable_avoiding u n (\<S> e (hd (stack e')))"
                unfolding post_dfs_def sub_env_def using ra_mono by auto
              with asm predfss \<open>stack e' = stack e\<close> True show ?thesis
                unfolding pre_dfss_def by auto
            next
              case False
              with asm predfss postdfsw \<open>stack e' = stack e\<close> show ?thesis
                by (auto simp: pre_dfss_def post_dfs_def)
            qed
          }

          ultimately show ?thesis
            unfolding pre_dfss_def by blast
        qed

        moreover have "post_dfss v (vs - {w}) e' (dfss v (vs - {w}) e')"
          using True \<open>e' = dfs w e\<close> calculation notexplored prepostdfss vs_case w_def by auto

        moreover have almost:"post_dfss v (vs - {w}) e' (dfss v vs e)"
          using calculation(2) calculation(4) by simp

        with postdfsw have "\<forall> w \<in> vs. \<forall> x. reachable w x \<longrightarrow> x \<in> visited (dfss v vs e)"
          by (auto simp: post_dfss_def post_dfs_def sub_env_def)

        moreover have "sub_env e (dfss v vs e)"
        proof -
          have "sub_env e e'"
            using post_dfs_def postdfsw by blast
          moreover have "sub_env e' (dfss v vs e)"
            using almost post_dfss_def by blast
          ultimately show ?thesis
            by (meson order_trans sub_env_def)
        qed
  
        moreover have "\<exists> ns. stack e = ns @ (stack (dfss v vs e))"
        proof -
          have "\<exists> ns. stack e = ns @ (stack e')"
            using post_dfs_def postdfsw by blast
          moreover have "\<exists> ns. stack e' = ns @ (stack (dfss v vs e))"
            using almost post_dfss_def by blast
          ultimately show ?thesis
            by fastforce
        qed

        moreover
        {
          fix n
          assume n: "n \<in> set (tl (stack (dfss v vs e)))"
          with almost have "\<S> (dfss v vs e) n = \<S> e' n"
            by (auto simp: post_dfss_def)
          moreover
          from almost n have "stack e' \<noteq> [] \<and> n \<in> set (tl (stack e'))"
            unfolding post_dfss_def
            by (metis Nil_is_append_conv Un_iff list.set_sel(2) self_append_conv2 set_append tl_append2)
          with postdfsw have "\<S> e' n = \<S> e n"
            unfolding post_dfs_def
            by (metis list.set_sel(2))
          ultimately have "\<S> (dfss v vs e) n = \<S> e n"
            by simp
        }

        ultimately show ?thesis
          by (simp add: post_dfss_def)
      next
        case False
        hence "e' = unite v w e" using notexplored
          using e'_def by simp
        from False have "w \<in> visited e"
          by simp
        from predfss have "wf_env e"
          by (simp add: pre_dfss_def)

        define pfx where "pfx = takeWhile (\<lambda>x. w \<notin> \<S> e x) (stack e)"
        define sfx where "sfx = dropWhile (\<lambda>x. w \<notin> \<S> e x) (stack e)"
        define cc where "cc = \<Union> {\<S> e x |x. x \<in> set pfx \<union> {hd sfx}}"

        have "stack e = pfx @ sfx"
            by (simp add: pfx_def sfx_def)

        have tl_sfx_not_in_cc:"\<forall> x \<in> set (tl sfx). x \<notin> cc"
        proof (clarify)
          fix x
          assume asm:"x \<in> set (tl sfx)" "x \<in> cc"
          from asm(2) obtain n where n_def:"n \<in> set pfx \<union> {hd sfx}" "x \<in> \<S> e n" using cc_def
            by blast
          have "n \<in> set (stack e)" using \<open>stack e = pfx @ sfx\<close> asm(1)
            by (metis Un_iff empty_set equals0D hd_in_set insertE list.sel(2) n_def(1) set_append)
          moreover have "x \<in> set (stack e)" using asm(1)
            by (metis list.sel(2) list.set_sel(2) set_dropWhileD sfx_def)
          moreover have "x \<noteq> n"
            by (smt (verit, best) IntI Un_iff \<open>stack e = pfx @ sfx\<close> asm(1) distinct.simps(2) distinct_append empty_iff empty_set list.exhaust_sel list.sel(2) list.set_sel(2) n_def(1) pre_dfss_def predfss singletonD wf_env_def)
          moreover have "\<S> e x \<inter> \<S> e n \<noteq> {}"
            by (smt (verit, best) equals0D inf_idem n_def(2) pre_dfss_def predfss wf_env_def)
          ultimately show False using predfss
            by (simp add: pre_dfss_def wf_env_def)
        qed

        obtain ww where ww_def: "ww \<in> set (stack e) \<and> w \<in> \<S> e ww" 
          using notexplored \<open>w \<in> visited e\<close> predfss unfolding pre_dfss_def wf_env_def
          by (smt (verit, ccfv_threshold) DiffI UnionE mem_Collect_eq)
        hence "ww \<in> set sfx"
          by (metis Un_iff set_append set_takeWhileD sfx_def takeWhile_dropWhile_id)
        hence "sfx \<noteq> []"
          by auto
        have "ww = hd sfx"
        proof (rule ccontr)
          assume "ww \<noteq> hd sfx"
          from \<open>ww \<in> set sfx\<close> have "w \<in> \<S> e (hd sfx)"
            unfolding sfx_def by (metis empty_iff empty_set hd_dropWhile)
          with ww_def \<open>wf_env e\<close> \<open>sfx \<noteq> []\<close> \<open>stack e = pfx @ sfx\<close> \<open>ww \<noteq> hd sfx\<close> 
          show "False"
            unfolding wf_env_def
            by (metis (no_types, lifting) Diff_cancel Diff_triv Un_iff insert_Diff insert_not_empty list.set_sel(1) set_append)
        qed
        with ww_def have "w \<in> \<S> e (hd sfx)"
          by simp

        have cc_scc: "is_subscc cc"
        proof (clarsimp simp: is_subscc_def)
          fix x y
          assume "x \<in> cc" "y \<in> cc"
          then obtain nx ny where
            nx: "nx \<in> set pfx \<union> {hd sfx}" "x \<in> \<S> e nx" and
            ny: "ny \<in> set pfx \<union> {hd sfx}" "y \<in> \<S> e ny"
            by (auto simp: cc_def)
          with \<open>wf_env e\<close>
          have "reachable x nx" "reachable ny y"
            by (auto simp: wf_env_def is_subscc_def)
          from wvs predfss have "reachable v w"
            by (auto simp: pre_dfss_def)
          from predfss 
          have "reachable (hd (stack e)) v"
            by (auto simp: pre_dfss_def wf_env_def is_subscc_def)
          from predfss have "stack e = hd (stack e) # tl (stack e)"
            by (auto simp: pre_dfss_def)
          with nx \<open>stack e = pfx @ sfx\<close> \<open>sfx \<noteq> []\<close>
          have "hd (stack e) \<preceq> nx in stack e"
            by (metis Un_iff Un_insert_right head_precedes list.exhaust_sel list.simps(15) set_append sup_bot.right_neutral)
          with \<open>wf_env e\<close> have "reachable nx (hd (stack e))"
            by (auto simp: wf_env_def)
          from \<open>stack e = pfx @ sfx\<close> \<open>sfx \<noteq> []\<close> \<open>ww = hd sfx\<close> ny
          have "ny \<preceq> ww in stack e" 
            by (metis List.set_insert empty_set insert_Nil list.exhaust_sel set_append split_list_precedes)
          with \<open>wf_env e\<close> have "reachable ww ny"
            by (auto simp: wf_env_def is_subscc_def)
          from ww_def \<open>wf_env e\<close> have "reachable w ww"
            by (auto simp: wf_env_def is_subscc_def)

          from \<open>reachable x nx\<close> \<open>reachable nx (hd (stack e))\<close>
               \<open>reachable (hd (stack e)) v\<close> \<open>reachable v w\<close>
               \<open>reachable w ww\<close> \<open>reachable ww ny\<close> \<open>reachable ny y\<close>
          show "reachable x y"
            using reachable_trans by meson
        qed

        have e'_def: "e' = e\<lparr>\<S> := \<lambda>x. if x \<in> cc then cc else \<S> e x, stack := sfx\<rparr>" using unite_def
          using \<open>e' = unite v w e\<close> cc_def pfx_def sfx_def by auto

        from \<open>sfx \<noteq> []\<close> have "stack e' = (hd sfx) # tl sfx"
          by (auto simp: e'_def)
        moreover
        from \<open>wf_env e\<close> \<open>sfx \<noteq> []\<close> have "\<S> e' (hd sfx) = cc"
          by (auto simp: wf_env_def cc_def e'_def)
        moreover
        from tl_sfx_not_in_cc have "\<forall>v \<in> set (tl sfx). \<S> e' v = \<S> e v"
          by (simp add: e'_def)
        ultimately
        have "(\<Union> {\<S> e' v | v. v \<in> set (stack e')}) 
              = cc \<union> (\<Union> {\<S> e v | v. v \<in> set (tl sfx)})"
          by auto
        moreover
        from \<open>stack e = pfx @ sfx\<close> \<open>sfx \<noteq> []\<close>
        have "stack e = pfx @ (hd sfx # tl sfx)"
          by auto
        ultimately
        have s_equal: "(\<Union> {\<S> e' v | v. v \<in> set (stack e')}) 
                       = (\<Union> {\<S> e v | v. v \<in> set (stack e)})"
          by (auto simp: cc_def)

        have "\<exists>ns. stack e = ns @ (stack e')" 
          using \<open>stack e = pfx @ sfx\<close> by (simp add: e'_def)

        moreover have "sub_env e e'"
        proof -
          have "\<forall> x. \<S> e x \<subseteq> \<S> e' x"
          proof -
            {
              fix x
              have "\<S> e x \<subseteq> \<S> e' x"
              proof (cases "x \<in> (set pfx) \<union> {hd sfx}")
                case True
                hence "\<S> e x \<subseteq> cc"
                  using cc_def by auto
                then show ?thesis using e'_def
                  by simp
              next
                case xFalse:False
                then show ?thesis
                proof (cases "x \<in> set (tl sfx)")
                  case True
                  hence "x \<notin> cc"
                  proof -
                    have "x \<in> set (stack e)" using True
                      by (metis \<open>ww \<in> set sfx\<close> empty_iff list.set_sel(2) set_dropWhileD set_empty2 sfx_def)
                    {
                      fix y
                      assume asm:"y \<in> set (pfx) \<or> y = hd sfx"
                      hence "x \<notin> \<S> e y"
                      proof (cases "y = hd sfx")
                        case True
                        hence "x \<noteq> y"
                          using xFalse by auto
                        then show ?thesis using predfss pre_dfss_def wf_env_def
                          by (smt (verit, ccfv_threshold) True \<open>ww \<in> set sfx\<close> \<open>x \<in> set (stack e)\<close> empty_iff empty_set inf.idem list.set_sel(1) set_dropWhileD sfx_def)
                      next  
                        case False
                        hence "y \<in> set pfx"
                          using asm by blast
                        then show ?thesis using True \<open>stack e = pfx @ sfx\<close> using \<open>x \<in> set (stack e)\<close> predfss unfolding pre_dfss_def wf_env_def
                        by (metis (mono_tags, lifting) xFalse UnI1 equals0D inf.idem pfx_def set_takeWhileD)
                      qed
                    }
                    then show ?thesis
                      using cc_def by blast
                  qed
                  then show ?thesis
                    by (simp add: e'_def)
                next
                  case False
                  hence "x \<notin> set (stack e)" using xFalse \<open>stack e = pfx @ sfx\<close>
                    by (metis Un_iff empty_set insert_iff list.exhaust_sel list.simps(15) set_append)
                  moreover have "stack e' = sfx" using e'_def
                    by simp
                  hence "x \<notin> set (stack e')"
                    using calculation set_dropWhileD sfx_def by fastforce
                  have "\<S> e' x = cc \<or> \<S> e x = \<S> e' x" using e'_def
                    by simp
                  then show ?thesis
                  proof (cases "\<S> e' x = cc")
                    case True
                    then show ?thesis
                    proof (cases "x \<in> visited e")
                      case True
                      then show ?thesis
                        by (smt (verit, ccfv_threshold) cc_def e'_def ext_inject mem_Collect_eq mem_simps(9) pre_dfss_def predfss subsetI surjective update_convs(1) update_convs(5) wf_env_def)
                    next
                      case False
                      then show ?thesis
                        using e'_def pre_dfss_def predfss wf_env_def by fastforce
                    qed
                  next
                    case False
                    then show ?thesis
                      using \<open>\<S> e' x = cc \<or> \<S> e x = \<S> e' x\<close> by force
                  qed
                qed
              qed
            }
            then show ?thesis
              by fastforce
          qed
          with s_equal show ?thesis
            by (simp add: sub_env_def e'_def)
        qed

      moreover have "pre_dfss v (vs - {w}) e'"
      proof -
        have "wf_env e'"
        proof -
          from e'_def \<open>wf_env e\<close> \<open>stack e = pfx @ sfx\<close>
          have "distinct (stack e')" 
               "set (stack e') \<subseteq> visited e'" 
               "explored e' \<subseteq> visited e'"
               "explored e' \<inter> set (stack e') = {}"
            by (auto simp: wf_env_def)

          moreover
          from \<open>wf_env e\<close> have "\<forall>v w. w \<in> \<S> e v \<longleftrightarrow> (\<S> e v = \<S> e w)"
            by (simp add: wf_env_def)
          with \<open>sub_env e e'\<close> have "\<forall>v w. w \<in> \<S> e' v \<longleftrightarrow> (\<S> e' v = \<S> e' w)"
            using e'_def cc_def
            by (smt (verit) select_convs(1) sub_env_def subset_eq surjective update_convs(1) update_convs(5))

          moreover have "\<forall>v \<in> set (stack e'). \<forall> w \<in> set (stack e'). v \<noteq> w \<longrightarrow> \<S> e' v \<inter> \<S> e' w = {}"
          proof -
            have "(\<forall>v w.  v \<preceq> w in stack e'\<and> v \<noteq> w \<longrightarrow> \<S> e' v \<inter> \<S> e' w = {}) \<longrightarrow> ?thesis"
              by (smt (verit, ccfv_threshold) Un_iff disjoint_iff_not_equal empty_set head_precedes list.sel(1) list.simps(15) precedes_append_left set_append split_list_last split_list_precedes)
            moreover have "\<forall>v w.  v \<preceq> w in stack e'\<and> v \<noteq> w \<longrightarrow> \<S> e' v \<inter> \<S> e' w = {}"
            proof (clarify)
              fix x y
              assume asm:"x \<preceq> y in stack e'" "x \<noteq> y"
              hence "x \<in> set (sfx)" "y \<in> set (sfx)"
                using e'_def precedes_mem(1)
                 apply (simp add: precedes_mem(1))
                using asm(1) e'_def precedes_mem(2) by force
              then show "\<S> e' x \<inter> \<S> e' y = {}"
              proof (cases "x = hd sfx")
                case True
                hence "y \<in> set (tl sfx)" using asm
                  by (metis True \<open>y \<in> set sfx\<close> emptyE empty_set list.exhaust_sel set_ConsD)
                hence "y \<notin> cc" using tl_sfx_not_in_cc
                  by blast
                moreover have "x \<in> cc" using True
                  by (smt (verit, del_insts) Un_iff cc_def mem_Collect_eq mem_simps(9) pre_dfss_def predfss singletonI wf_env_def)
                ultimately show ?thesis
                  by (smt (verit, best) \<open>\<forall>v w. (w \<in> \<S> e' v) = (\<S> e' v = \<S> e' w)\<close> disjoint_iff e'_def select_convs(1) surjective update_convs(1) update_convs(5))
              next
                case False
                hence "x \<in> set (tl sfx)"
                  by (metis \<open>x \<in> set sfx\<close> emptyE empty_set list.exhaust_sel set_ConsD)
                moreover have "y \<in> set (tl sfx)" using asm(1) calculation
                  by (smt (verit, best) IntI \<open>\<exists>ns. stack e = ns @ stack e'\<close> \<open>stack e = pfx @ sfx\<close> \<open>y \<in> set sfx\<close> asm(2) distinct_append emptyE in_set_member list.distinct(1) list.exhaust_sel list.sel(2) member_rec(1) pre_dfss_def precedes_append_left precedes_append_left_iff predfss tail_not_precedes wf_env_def)
                moreover have "\<S> e x = \<S> e' x" using tl_sfx_not_in_cc calculation(1)
                  by (simp add: e'_def)
                moreover have "\<S> e y = \<S> e' y" using tl_sfx_not_in_cc calculation(2)
                  by (simp add: e'_def)
                ultimately show ?thesis using \<open>x \<noteq> y\<close> predfss
                  by (smt (verit, ccfv_threshold) \<open>x \<in> set sfx\<close> \<open>y \<in> set sfx\<close> pre_dfss_def set_dropWhileD sfx_def wf_env_def)
              qed
            qed
            ultimately show ?thesis
              by meson
          qed

          moreover 
          { 
            fix u
            assume "u \<notin> visited e'"
            hence "u \<notin> visited e"
              by (simp add: e'_def)
            with \<open>wf_env e\<close> have "\<S> e u = {u}"
              by (auto simp: wf_env_def)
            moreover
            from \<open>u \<notin> visited e\<close> \<open>wf_env e\<close> \<open>ww = hd sfx\<close> \<open>stack e = pfx @ sfx\<close> ww_def
            have "u \<notin> set pfx \<union> {hd sfx}"
              unfolding wf_env_def
              by (metis Un_iff set_append singletonD subset_eq)
            with \<open>wf_env e\<close> \<open>\<S> e u = {u}\<close> have "u \<notin> cc"
              unfolding wf_env_def cc_def by auto
            ultimately have "\<S> e' u = {u}"
              by (simp add: e'_def)
          }

          moreover 
          from s_equal \<open>wf_env e\<close>
          have "\<Union> {\<S> e' v | v. v \<in> set (stack e')} 
                = visited e' - explored e'"
            by (simp add: wf_env_def e'_def)

          moreover have "\<forall> x y. x \<preceq> y in stack e' \<longrightarrow> reachable y x"
            by (smt (verit, best) \<open>\<exists>ns. stack e = ns @ stack e'\<close> pre_dfss_def precedes_append_left predfss wf_env_def)
          moreover 
          from cc_scc \<open>wf_env e\<close> have "\<forall> x. is_subscc (\<S> e' x)" 
            by (auto simp: wf_env_def e'_def)
          moreover have "\<forall> x \<in> explored e'. \<forall> y. reachable x y \<longrightarrow> y \<in> explored e'"
            using e'_def pre_dfss_def predfss wf_env_def by fastforce
          moreover have "\<forall> S \<in> sccs e'. is_scc S" using e'_def
            using pre_dfss_def predfss wf_env_def by fastforce

          ultimately show ?thesis unfolding wf_env_def
            by blast
        qed

        moreover have "v \<in> visited e'"
          by (metis \<open>sub_env e e'\<close> in_mono pre_dfss_def predfss sub_env_def)

        moreover have "vs - {w} \<subseteq> successors v"
          by (metis Diff_subset pre_dfss_def predfss subset_trans)

        moreover have "\<forall> n \<in> set (stack e'). reachable n v"
          by (metis Un_iff \<open>\<exists>ns. stack e = ns @ stack e'\<close> pre_dfss_def predfss set_append)

        moreover have "stack e' \<noteq> []"
        proof -
          have "stack e' = sfx"
            by (simp add: e'_def)
          from \<open>ww \<in> set (sfx)\<close> have "sfx \<noteq> []"
            by fastforce
          then show ?thesis using \<open>w \<in> \<S> e (hd sfx)\<close>
            using \<open>stack e' = sfx\<close> by fastforce
        qed

        moreover 
        {
          fix u
          assume "u \<in> successors v - (vs - {w})"
          have "u \<in> explored e' \<union> \<S> e' (hd (stack e'))"
            sorry
        }

        moreover have "v \<in> \<S> e' (hd (stack e'))"
        proof -
          have "w \<in> \<S> e (hd sfx)"
          proof -
            have "ww = hd sfx"
            proof (rule ccontr)
              assume asm:"ww \<noteq> hd (sfx)"
              from \<open>ww \<in> set sfx\<close> obtain n where n_def:"n = hd sfx"
                by simp
              have "w \<in> \<S> e n" using n_def predfss sfx_def ww_def unfolding pre_dfss_def wf_env_def
                by (metis \<open>ww \<in> set sfx\<close> empty_iff empty_set hd_dropWhile)
              hence "ww \<in> \<S> e n" using ww_def predfss
                by (simp add: pre_dfss_def wf_env_def)
              hence "\<S> e n = \<S> e ww" using predfss
                by (simp add: pre_dfss_def wf_env_def)
              moreover have "n \<noteq> ww"
                using asm n_def by blast
              moreover have "n \<in> set (stack e)" "ww \<in> set (stack e)"
                apply (metis \<open>ww \<in> set sfx\<close> emptyE empty_set hd_in_set n_def set_dropWhileD sfx_def)
                by (simp add: ww_def)
              moreover have "\<S> e ww \<inter> \<S> e n = {}" using predfss unfolding pre_dfss_def wf_env_def
                using calculation(2) calculation(3) calculation(4) by auto
              ultimately show False
                using ww_def by blast
            qed
          then show ?thesis
            by (simp add: \<open>w \<in> \<S> e (hd sfx)\<close>)
        qed

        moreover have "hd (stack e') = hd sfx"
          by (simp add: e'_def)

        moreover have "w \<in> \<S> e' (hd (stack e'))"
          using \<open>sub_env e e'\<close> calculation(1) calculation(2) sub_env_def by fastforce

        moreover have "w \<in> cc"
          using calculation(1) cc_def by blast

        ultimately show ?thesis
          using e'_def apply auto
          apply (smt (verit, del_insts) UnCI \<open>stack e = pfx @ sfx\<close> append_self_conv2 cc_def hd_append2 hd_in_set insert_iff mem_Collect_eq mem_simps(9) pre_dfss_def predfss)
          by (smt (verit, del_insts) cc_def mem_Collect_eq mem_simps(9) pre_dfss_def predfss wf_env_def)
      qed

      moreover
      {
        fix n u
        assume "n \<in> set (tl (stack e'))" "u \<in> \<S> e' (hd (stack e')) - {v}"
               "reachable_avoiding u n (\<S> e' (hd (stack e')))"
        have "False"
          sorry
      }

      ultimately show ?thesis
        unfolding pre_dfss_def by blast
    qed

    moreover have "dfss v vs e = dfss v (vs - {w}) e'"
      using False \<open>e' = unite v w e\<close> dfss.psimps dom notexplored vs_case w_def by force
    moreover have "post_dfss v (vs - {w}) e' (dfss v (vs - {w}) e')"
      using False \<open>e' = unite v w e\<close> calculation notexplored prepostdfss vs_case w_def
      by (simp add: pre_dfss_def)
    moreover have "post_dfss v vs e (dfss v (vs-{w}) e')" sorry

    ultimately show ?thesis
      by simp
  qed
qed


end
end