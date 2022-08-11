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
  root :: "'v"
  \<S> :: "'v \<Rightarrow> 'v set"
  explored :: "'v set"
  visited :: "'v set"
  vsuccs :: "'v \<Rightarrow> 'v set"
  sccs :: "'v set set"
  stack :: "'v list"
  cstack :: "'v list"


section \<open>Auxiliary lemmas about lists\<close>

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
  certain edges. More precisely, @{text y} is reachable from @{text x}
  avoiding @{text E} if there exists a path such that no edge from
  @{text E} appears along the path.
\<close>
inductive reachable_avoiding where
  ra_refl[iff]: "reachable_avoiding x x E"
| ra_succ[elim]: "\<lbrakk>reachable_avoiding x y E; edge y z; (y,z) \<notin> E\<rbrakk> \<Longrightarrow> reachable_avoiding x z E"

lemma edge_ra:
  assumes "edge x y" and "(x,y) \<notin> E"
  shows "reachable_avoiding x y E"
  using assms by (meson reachable_avoiding.simps)

lemma ra_trans:
  assumes 1: "reachable_avoiding x y E" and 2: "reachable_avoiding y z E"
  shows "reachable_avoiding x z E"
  using 2 1 by induction auto

lemma ra_cases:
  assumes "reachable_avoiding x y E"
  shows "x=y \<or> (\<exists>z. z \<in> successors x \<and> (x,z) \<notin> E \<and> reachable_avoiding z y E)"
using assms proof (induction)
  case (ra_refl x S)
  then show ?case by simp
next
  case (ra_succ x y S z)
  then show ?case
    by (metis ra_refl reachable_avoiding.ra_succ)
qed

lemma ra_mono: 
  assumes "reachable_avoiding x y E" and "E' \<subseteq> E"
  shows "reachable_avoiding x y E'"
using assms by induction auto

lemma ra_add_edge:
  assumes "reachable_avoiding x y E"
  shows "reachable_avoiding x y (E \<union> {(v,w)})
         \<or> (reachable_avoiding x v (E \<union> {(v,w)}) \<and> reachable_avoiding w y (E \<union> {(v,w)}))"
using assms proof (induction)
  case (ra_refl x E)
  then show ?case by simp
next
  case (ra_succ x y E z)
  then show ?case
    using reachable_avoiding.ra_succ by auto
qed


text \<open>
  Reachability avoiding some edges obviously implies reachability.
  Conversely, reachability implies reachability avoiding the empty set.
\<close>
lemma ra_reachable:
  "reachable_avoiding x y E \<Longrightarrow> reachable x y"
  by (induction rule: reachable_avoiding.induct) (auto intro: succ_reachable)

lemma ra_empty:
  "reachable_avoiding x y {} = reachable x y"
proof
  assume "reachable_avoiding x y {}"
  thus "reachable x y"
    by (rule ra_reachable)
next
  assume "reachable x y"
  hence "reachable_end x y"
    by (rule reachable_re)
  thus "reachable_avoiding x y {}"
    by induction auto
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
  using assms unfolding is_scc_def 
  by (metis insertI1 subscc_add subset_insertI)

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

function (domintros) dfs :: "'v \<Rightarrow> 'v env \<Rightarrow> 'v env" and dfss :: "'v \<Rightarrow> 'v env \<Rightarrow> 'v env" where
  "dfs v e =
  (let e1 = e\<lparr>visited := visited e \<union> {v}, stack := (v # stack e), cstack := (v # cstack e)\<rparr>;
       e' = dfss v e1
   in if v = hd(stack e')
      then e'\<lparr>sccs := sccs e' \<union> {\<S> e' v}, 
              explored := explored e' \<union> (\<S> e' v), 
              stack := tl(stack e'), cstack := tl(cstack e')\<rparr>
      else e'\<lparr>cstack := tl(cstack e')\<rparr>)"
| "dfss v e =
   (let vs = successors v - vsuccs e v
    in  if vs = {} then e
        else let w = SOME x. x \<in> vs;
                 e' = (if w \<in> explored e then e
                       else if w \<notin> visited e
                       then dfs w e
                       else unite v w e);
                 e'' = (e'\<lparr>vsuccs := 
                             (\<lambda>x. if x=v then vsuccs e' v \<union> {w} 
                                  else vsuccs e' x)\<rparr>)
             in  dfss v e'')"
  by pat_completeness (force+)

section \<open>Definition of the predicates used in the correctness proof\<close>

text \<open>
  Set of edges starting from some node in the
  equivalence class of node that have not yet been followed.
\<close>
definition unvisited where
  "unvisited e x \<equiv> 
   {(a,b) | a b. a \<in> \<S> e x \<and> b \<in> successors a - vsuccs e a}"

text \<open>
  The following definition characterizes Well-formed environments.
  This predicate will be shown to hold throughout the execution
  of the algorithm.
\<close>
definition wf_env where
  "wf_env e \<equiv>
    distinct (stack e)
  \<and> (\<forall>v \<in> visited e. reachable (root e) v)
  \<and> set (stack e) \<subseteq> visited e
  \<and> explored e \<subseteq> visited e
  \<and> explored e \<inter> set (stack e) = {}
  \<and> (\<forall>v. vsuccs e v \<subseteq> successors v)
  \<and> (\<forall>v. vsuccs e v \<subseteq> visited e)
  \<and> (\<forall>v. v \<notin> visited e \<longrightarrow> vsuccs e v = {})
  \<and> (\<forall>v. v \<in> explored e \<longrightarrow> vsuccs e v = successors v)
  \<and> (\<forall>v w. w \<in> \<S> e v \<longleftrightarrow> (\<S> e v = \<S> e w))
  \<and> (\<forall>v \<in> set (stack e). \<forall> w \<in> set (stack e). v \<noteq> w \<longrightarrow> \<S> e v \<inter> \<S> e w = {})
  \<and> (\<forall> v. v \<notin> visited e \<longrightarrow> \<S> e v = {v})
  \<and> \<Union> {\<S> e v | v. v \<in> set (stack e)} = visited e - explored e
  \<and> (\<forall> x y. x \<preceq> y in stack e \<longrightarrow> reachable y x)
  \<and> (\<forall>x y. x \<preceq> y in stack e \<and> x \<noteq> y \<longrightarrow>
        (\<forall>u \<in> \<S> e x. \<not> reachable_avoiding u y (unvisited e x)))
  \<and> (\<forall> x. is_subscc (\<S> e x))
  \<and> (\<forall> x \<in> explored e. \<forall> y. reachable x y \<longrightarrow> y \<in> explored e)  
  \<and> (\<forall> S \<in> sccs e. is_scc S)
  \<and> \<Union> (sccs e) = explored e
  \<and> (distinct (cstack e))
  \<and> (set (cstack e) \<subseteq> visited e)
  \<and> (\<forall>n \<in> visited e - set (cstack e). vsuccs e n = successors n)
  \<and> (\<forall>n m. n \<preceq> m in stack e \<longrightarrow> n \<preceq> m in cstack e)
  \<and> (\<forall>n \<in> set (stack e). \<forall>m \<in> \<S> e n. m \<in> set (cstack e) \<longrightarrow> m \<preceq> n in cstack e)
"
(* Last 3 clauses
- the node is popped from the call stack only after all successors have been explored
- the equivalence class stack is a sub-sequence of the call stack
- the representative of an equivalence class is the oldest node in the sense of the call order
*)


text \<open>
  If @{text w} is reachable from visited node @{text v}, but
  no unvisited successor of a node reachable from @{text v}
  can reach @{text w}, then @{text w} must be visited.
\<close>
lemma reachable_visited:
  assumes e: "wf_env e"
      and v: "v \<in> visited e"
      and w: "reachable v w"
      and s: "\<forall>n \<in> visited e. \<forall>m \<in> successors n - vsuccs e n. 
                 reachable v n \<longrightarrow> \<not> reachable m w"
  shows "w \<in> visited e"
using w v s proof (induction)
  case (reachable_refl x)
  then show ?case by simp
next
  case (reachable_succ x y z)
  then have "y \<in> vsuccs e x" by blast
  with e have "y \<in> visited e" 
    unfolding wf_env_def by (meson subsetD)
  with reachable_succ reachable.reachable_succ show ?case
    by blast
qed

text \<open>
  Edges towards explored nodes do not contribute to reachability
  of unexplored nodes avoiding some set of edges.
\<close>
lemma avoiding_explored:
  assumes e: "wf_env e"
      and xy: "reachable_avoiding x y E"
      and y: "y \<notin> explored e"
      and w: "w \<in> explored e"
    shows "reachable_avoiding x y (E \<union> {(v,w)})"
using xy y proof (induction)
  case (ra_refl x E)
  then show ?case by simp
next
  case (ra_succ x y E z)
  from e \<open>z \<in> successors y\<close> \<open>z \<notin> explored e\<close>
  have "y \<notin> explored e"
    unfolding wf_env_def by (meson reachable_edge)
  with ra_succ.IH have "reachable_avoiding x y (E \<union> {(v,w)})" .
  moreover
  from w \<open>(y,z) \<notin> E\<close> \<open>z \<notin> explored e\<close> have "(y,z) \<notin> E \<union> {(v,w)}"
    by auto
  ultimately show ?case 
    using  \<open>z \<in> successors y\<close> by auto
qed

text \<open>
  An ordering on environments.
\<close>
definition sub_env where
  "sub_env e e' \<equiv> 
     root e' = root e
   \<and> visited e \<subseteq> visited e'
   \<and> explored e \<subseteq> explored e'
   \<and> (\<forall>v. vsuccs e v \<subseteq> vsuccs e' v)
   \<and> (\<forall> v. \<S> e v \<subseteq> \<S> e' v)
   \<and> (\<Union> {\<S> e v | v . v \<in> set (stack e)})
     \<subseteq> (\<Union> {\<S> e' v | v . v \<in> set (stack e')})
"

lemma sub_env_trans:
  assumes "sub_env e e'" and "sub_env e' e''"
  shows "sub_env e e''"
  using assms unfolding sub_env_def
  by (metis (no_types, lifting) subset_trans)

text \<open>
  Pre- and post-conditions for function dfs.
\<close>
definition pre_dfs where 
  "pre_dfs v e \<equiv> 
     wf_env e
   \<and> v \<notin> visited e
   \<and> reachable (root e) v
   \<and> vsuccs e v = {}
   \<and> (\<forall>n \<in> set (stack e). reachable n v)"

definition post_dfs where 
  "post_dfs v prev_e e \<equiv> 
     wf_env e
   \<and> v \<in> visited e
   \<and> sub_env prev_e e
   \<and> vsuccs e v = successors v
   \<and> (\<forall>w \<in> visited prev_e. vsuccs e w = vsuccs prev_e w)
   \<and> (\<forall>n \<in> set (stack e). reachable n v)
   \<and> (\<exists>ns. stack prev_e = ns @ (stack e))
   \<and> ((v \<in> explored e \<and> stack e = stack prev_e \<and> (\<forall>n \<in> set (stack e). \<S> e n = \<S> prev_e n)) 
       \<or> (stack e \<noteq> [] \<and> v \<in> \<S> e (hd (stack e)) 
          \<and> (\<forall>n \<in> set (tl (stack e)). \<S> e n = \<S> prev_e n)))
   \<and> cstack e = cstack prev_e
"

text \<open>
  Pre- and post-conditions for function dfss.
\<close>
definition pre_dfss where 
  "pre_dfss v e \<equiv> 
     wf_env e 
   \<and> v \<in> visited e
   \<and> (\<forall>w \<in> vsuccs e v. w \<in> explored e \<union> \<S> e (hd (stack e)))
   \<and> (\<forall>n \<in> set (stack e). reachable n v)
   \<and> (stack e \<noteq> [])
   \<and> (v \<in> \<S> e (hd (stack e)))
   \<and> (\<exists>ns. cstack e = v # ns)
"

definition post_dfss where 
  "post_dfss v prev_e e \<equiv> 
     wf_env e
   \<and> vsuccs e v = successors v
   \<and> (\<forall>w \<in> visited prev_e - {v}. vsuccs e w = vsuccs prev_e w)
   \<and> sub_env prev_e e
   \<and> (\<forall>w \<in> successors v. w \<in> explored e \<union> \<S> e (hd (stack e)))
   \<and> (\<forall> n \<in> set (stack e). reachable n v)
   \<and> (stack e \<noteq> [])
   \<and> (\<exists> ns. stack prev_e = ns @ (stack e))
   \<and> (v \<in> \<S> e (hd (stack e)))
   \<and> (\<forall>n \<in> set (tl (stack e)). \<S> e n = \<S> prev_e n)
   \<and> (hd (stack e) = v \<longrightarrow> (\<forall>n \<in> set (tl (stack e)). \<not> reachable v n))
   \<and> cstack e = cstack prev_e
"

section \<open>Proof of partial correctness\<close>

text \<open>
  The precondition of function @{text dfs} ensures the precondition
  of @{text dfss} at the call of that function.
\<close>
lemma pre_dfs_pre_dfss:
  assumes "pre_dfs v e"
  shows "pre_dfss v (e\<lparr> visited := visited e \<union> {v}, stack := v # stack e, cstack := v # cstack e\<rparr>)"
        (is "pre_dfss v ?e'")
proof -
  have "distinct (stack ?e')"
       "\<forall>v \<in> visited ?e'. reachable (root ?e') v"
       "set (stack ?e') \<subseteq> visited ?e'"
       "explored ?e' \<subseteq> visited ?e'"
       "\<forall>v. vsuccs ?e' v \<subseteq> successors v"
       "\<forall>v. vsuccs ?e' v \<subseteq> visited ?e'"
       "\<forall>v. v \<notin> visited ?e' \<longrightarrow> vsuccs ?e' v = {}"
       "explored ?e' \<inter> set (stack ?e') = {}"
       "(\<forall>w z. z \<in> \<S> ?e' w \<longleftrightarrow> (\<S> ?e' w = \<S> ?e' z))"
       "(\<forall> v. v \<notin> visited ?e' \<longrightarrow> \<S> ?e' v = {v})"
    using assms unfolding pre_dfs_def wf_env_def by auto

  moreover
  have "(\<forall>v \<in> set (stack ?e'). \<forall> w \<in> set (stack ?e'). v \<noteq> w \<longrightarrow> \<S> ?e' v \<inter> \<S> ?e' w = {})"
  proof (clarify)
    fix x y
    assume asm: "x \<in> set (stack ?e')" "y \<in> set (stack ?e')" "x \<noteq> y"
    show "\<S> ?e' x \<inter> \<S> ?e' y = {}"
    proof (cases "x=v")
      case True
      with assms have "\<S> ?e' x = {v}"
        by (auto simp: pre_dfs_def wf_env_def)
      with True asm assms \<open>\<forall>w z. (z \<in> \<S> ?e' w) \<longleftrightarrow> (\<S> ?e' w = \<S> ?e' z)\<close> 
      show ?thesis
        unfolding pre_dfs_def wf_env_def
        by (smt (verit) disjoint_iff singleton_iff)
    next
      case False
      show ?thesis
      proof (cases "y = v")
        case True
        with assms have "\<S> ?e' y = {v}"
          by (auto simp: pre_dfs_def wf_env_def)
        with True asm assms \<open>\<forall>w z. (z \<in> \<S> ?e' w) \<longleftrightarrow> (\<S> ?e' w = \<S> ?e' z)\<close> 
        show ?thesis
          unfolding pre_dfs_def wf_env_def
          by (smt (verit) disjoint_iff singleton_iff)
      next
        case False
        with \<open>x \<noteq> v\<close> assms asm show ?thesis
          by (auto simp: pre_dfs_def wf_env_def)
      qed
    qed
  qed

  moreover 
  have "\<forall>u. u \<in> explored ?e' \<longrightarrow> vsuccs ?e' u = successors u"
    using assms by (auto simp: pre_dfs_def wf_env_def)

  moreover
  have "\<Union> {\<S> ?e' v | v . v \<in> set (stack ?e')} = visited ?e' - explored ?e'"
  proof -
    have "\<Union> {\<S> ?e' v | v . v \<in> set (stack ?e')} = 
          (\<Union> {\<S> ?e' v | v . v \<in> set (stack e)}) \<union> \<S> e v"
      by auto
    also have "\<dots> = visited ?e' - explored ?e'"
      using assms unfolding pre_dfs_def wf_env_def by auto
    finally show ?thesis .
  qed

  moreover
  have "\<forall> x y. x \<preceq> y in stack ?e' \<longrightarrow> reachable y x"
  proof (clarify)
    fix x y
    assume "x \<preceq> y in stack ?e'"
    show "reachable y x"
    proof (cases "x=v")
      assume "x=v"
      with \<open>x \<preceq> y in stack ?e'\<close> assms show ?thesis
        apply (auto simp: pre_dfs_def)
        by (metis insert_iff list.simps(15) precedes_mem(2) reachable_refl)
    next
      assume "x \<noteq> v"
      with \<open>x \<preceq> y in stack ?e'\<close>
      have "x \<preceq> y in stack e"
        by (simp add: precedes_in_tail)
      with assms show ?thesis
        by (simp add: pre_dfs_def wf_env_def)
    qed
  qed

  moreover
  have "\<forall> x. is_subscc (\<S> ?e' x)" using assms
    unfolding pre_dfs_def wf_env_def by simp

  moreover
  have "\<forall> x \<in> explored ?e'. \<forall> y. reachable x y \<longrightarrow> y \<in> explored ?e'"
  proof -
    have "explored ?e' = explored e" by simp
    then show ?thesis using assms unfolding wf_env_def
      by (simp add: pre_dfs_def wf_env_def) 
  qed

  moreover
  have "\<forall>x y. x \<preceq> y in stack ?e' \<and> x \<noteq> y \<longrightarrow>
           (\<forall>u \<in> \<S> ?e' x. \<not> reachable_avoiding u y (unvisited ?e' x))"
  proof (clarify)
    fix x y u
    assume asm: "x \<preceq> y in stack ?e'" "x \<noteq> y" "u \<in> \<S> ?e' x"
                "reachable_avoiding u y (unvisited ?e' x)"
    show "False"
    proof (cases "x = v")
      case True
      with assms \<open>u \<in> \<S> ?e' x\<close> have "u = v" "vsuccs ?e' v = {}"
        by (auto simp: pre_dfs_def wf_env_def)
      with \<open>reachable_avoiding u y (unvisited ?e' x)\<close>[THEN ra_cases]
           True \<open>x \<noteq> y\<close> assms
      show ?thesis
        by (auto simp: pre_dfs_def wf_env_def unvisited_def)
    next
      case False
      with \<open>x \<preceq> y in stack ?e'\<close> have "x \<preceq> y in stack e"
        by (simp add: precedes_in_tail)
      with asm assms show ?thesis
        by (auto simp: pre_dfs_def wf_env_def unvisited_def)
    qed
  qed

  moreover
  have "\<forall> S \<in> sccs ?e'. is_scc S"
  proof (clarify)
    fix S
    assume asm:"S \<in> sccs ?e'"
    have "sccs e = sccs ?e'" by simp
    moreover have "S \<in> sccs e" using asm by simp
    thus "is_scc S" using assms asm pre_dfs_def wf_env_def[of e]
      by blast
  qed

  moreover
  from assms have "\<Union> (sccs ?e') = explored ?e'"
    by (auto simp: pre_dfs_def wf_env_def)

  moreover 
  from assms have "distinct (cstack ?e')"
    by (auto simp: pre_dfs_def wf_env_def)

  moreover 
  from assms have "set (cstack ?e') \<subseteq> visited ?e'"
    by (auto simp: pre_dfs_def wf_env_def)

  moreover 
  from assms
  have "\<forall>n \<in> visited ?e' - set(cstack ?e'). vsuccs ?e' n = successors n"
    by (auto simp: pre_dfs_def wf_env_def)

  moreover 
  have "\<forall>n m. n \<preceq> m in stack ?e' \<longrightarrow> n \<preceq> m in cstack ?e'"
  proof (clarsimp)
    fix n m
    assume "n \<preceq> m in (v # stack e)"
    with assms show "n \<preceq> m in (v # cstack e)"
      unfolding pre_dfs_def wf_env_def
      by (metis head_precedes insertI1 list.simps(15) precedes_in_tail precedes_mem(2) precedes_refl)
  qed

  moreover 
  have "\<forall>n \<in> set (stack ?e'). \<forall> m \<in> \<S> ?e' n. m \<in> set (cstack ?e') \<longrightarrow> m \<preceq> n in cstack ?e'"
  proof (clarify)
    fix n m
    assume "n \<in> set (stack ?e')" "m \<in> \<S> ?e' n" "m \<in> set (cstack ?e')"
    show "m \<preceq> n in cstack ?e'"
    proof (cases "n = v")
      case True
      with assms \<open>m \<in> \<S> ?e' n\<close> have "m = v"
        by (auto simp: pre_dfs_def wf_env_def)
      then show ?thesis by (simp add: True)
    next
      case False
      with \<open>n \<in> set (stack ?e')\<close> \<open>m \<in> \<S> ?e' n\<close>
      have "n \<in> set (stack e)" "m \<in> \<S> e n"
        by auto
      moreover
      from assms False \<open>m \<in> \<S> e n\<close>
      have "m \<noteq> v"
        unfolding pre_dfs_def wf_env_def
        by (metis singletonD)
      with \<open>m \<in> set (cstack ?e')\<close> have "m \<in> set (cstack e)"
        by simp
      ultimately have "m \<preceq> n in cstack e"
        using assms by (auto simp: pre_dfs_def wf_env_def)
      thus ?thesis
        by (simp add: \<open>m \<noteq> v\<close> precedes_in_tail)
    qed
  qed

  ultimately have "wf_env ?e'"
    unfolding wf_env_def by blast

  moreover
  have "v \<in> visited ?e'"
    by simp

  moreover
  from assms 
  have "\<forall>w \<in> vsuccs ?e' v. w \<in> explored ?e' \<union> \<S> ?e' (hd (stack ?e'))"
    by (simp add: pre_dfs_def)

  moreover
  have reachstack:"\<forall> n \<in> set (stack ?e'). reachable n v"
    by (simp add: \<open>\<forall>x y. x \<preceq> y in stack ?e' \<longrightarrow> reachable y x\<close> head_precedes)

  moreover
  have notempty: "stack ?e' \<noteq> []"
    by simp

  moreover
  from \<open>pre_dfs v e\<close> have "\<S> ?e' (hd (stack ?e')) = {v}"
    by (simp add: pre_dfs_def wf_env_def)

  moreover
  have "\<exists>ns. cstack ?e' = v # ns"
    by auto

  ultimately show ?thesis
    unfolding pre_dfss_def by blast
qed

text \<open>
  Function @{text unite} maintains monotonicity on environments w.r.t.
  the @{text sub_env} relation.
\<close>

lemma unite_mono:
  fixes e v w
  defines "e' \<equiv> unite v w e"
  assumes pre: "pre_dfss v e"
        and w: "w \<in> successors v" "w \<notin> vsuccs e v" "w \<in> visited e" "w \<notin> explored e"
  shows "sub_env e e'"
proof -
  from pre have wf: "wf_env e"
    by (simp add: pre_dfss_def)
  
  define pfx where "pfx = takeWhile (\<lambda>x. w \<notin> \<S> e x) (stack e)"
  define sfx where "sfx = dropWhile (\<lambda>x. w \<notin> \<S> e x) (stack e)"
  define cc where "cc = \<Union> {\<S> e x |x. x \<in> set pfx \<union> {hd sfx}}"

  have "stack e = pfx @ sfx"
    by (simp add: pfx_def sfx_def)

  have cc_Un: "cc = \<Union> {\<S> e x | x. x \<in> cc}"
  proof
    {
      fix n
      assume "n \<in> cc"
      with wf have "n \<in> \<Union> {\<S> e x | x. x \<in> cc}"
        unfolding wf_env_def cc_def
        by (smt (verit, ccfv_threshold) Union_iff mem_Collect_eq)
    }
    thus "cc \<subseteq> \<Union> {\<S> e x | x. x \<in> cc}" ..
  next
    {
      fix n x
      assume "x \<in> cc" "n \<in> \<S> e x"
      with \<open>wf_env e\<close> have "n \<in> cc"
        unfolding wf_env_def cc_def
        by (smt (verit) Union_iff mem_Collect_eq)
    }
    thus "(\<Union> {\<S> e x | x. x \<in> cc}) \<subseteq> cc"
      by blast
  qed

  from wf w have "w \<in> \<Union> {\<S> e n | n. n \<in> set (stack e)}"
    by (simp add: wf_env_def)
  then obtain n where "n \<in> set (stack e)" "w \<in> \<S> e n"
    by auto
  hence sfx: "sfx \<noteq> [] \<and> w \<in> \<S> e (hd sfx)"
    unfolding sfx_def
    by (metis dropWhile_eq_Nil_conv hd_dropWhile)
  with \<open>wf_env e\<close> \<open>stack e = pfx @ sfx\<close> 
  have pfx: "set pfx \<union> {hd sfx} \<subseteq> cc"
    unfolding wf_env_def cc_def 
    by (smt (verit) Union_iff mem_Collect_eq subset_eq)

  from pre \<open>stack e = pfx @ sfx\<close> sfx
  have "v \<in> cc"
    unfolding pre_dfss_def cc_def
    by (smt (verit, ccfv_threshold) Un_iff UnionI hd_append2 insert_iff list.set_sel(1) mem_Collect_eq self_append_conv2)

  have tl_int_cc: "\<forall>n \<in> set (tl sfx). \<S> e n \<inter> cc = {}"
  proof -
    {
      fix n u
      assume "n \<in> set (tl sfx)" "u \<in> \<S> e n" "u \<in> cc"
      from sfx \<open>n \<in> set (tl sfx)\<close> \<open>stack e = pfx @ sfx\<close> wf
      have n: "n \<in> set (stack e) - (set pfx \<union> {hd sfx})"
        unfolding wf_env_def
        by (metis Diff_iff Int_iff Un_iff distinct.simps(2) distinct_append empty_iff list.exhaust_sel list.set_sel(2) set_append singletonD)
      from \<open>u \<in> cc\<close> obtain n' where
        n': "n' \<in> set pfx \<union> {hd sfx}" "u \<in> \<S> e n'"
        by (auto simp: cc_def)
      with n \<open>stack e = pfx @ sfx\<close> sfx wf
      have "\<S> e n \<inter> \<S> e n' = {}"
        unfolding wf_env_def
        by (metis (no_types, lifting) DiffE UnCI UnE list.set_sel(1) set_append singleton_iff)
      with \<open>u \<in> \<S> e n\<close> \<open>u \<in> \<S> e n'\<close> have "False"
        by auto
    }
    thus ?thesis by auto
  qed

  with wf sfx \<open>stack e = pfx @ sfx\<close>
  have tl_sfx_not_in_cc: "\<forall>x \<in> set (tl sfx). x \<notin> cc"
    unfolding wf_env_def cc_def
    by (metis (no_types, lifting) disjoint_insert(1) insert_Diff)

  have cc_scc: "is_subscc cc"
  proof (clarsimp simp: is_subscc_def)
    fix x y
    assume "x \<in> cc" "y \<in> cc"
    then obtain nx ny where
      nx: "nx \<in> set pfx \<union> {hd sfx}" "x \<in> \<S> e nx" and
      ny: "ny \<in> set pfx \<union> {hd sfx}" "y \<in> \<S> e ny"
      by (auto simp: cc_def)
    with wf have "reachable x nx" "reachable ny y"
      by (auto simp: wf_env_def is_subscc_def)
    from w pre have "reachable v w"
      by (auto simp: pre_dfss_def)
    from pre have "reachable (hd (stack e)) v"
      by (auto simp: pre_dfss_def wf_env_def is_subscc_def)
    from pre have "stack e = hd (stack e) # tl (stack e)"
      by (auto simp: pre_dfss_def)
    with nx \<open>stack e = pfx @ sfx\<close> sfx
    have "hd (stack e) \<preceq> nx in stack e"
      by (metis Un_iff Un_insert_right head_precedes list.exhaust_sel list.simps(15) set_append sup_bot.right_neutral)
    with wf have "reachable nx (hd (stack e))"
      by (auto simp: wf_env_def)
    from \<open>stack e = pfx @ sfx\<close> sfx ny
    have "ny \<preceq> hd sfx in stack e" 
      by (metis List.set_insert empty_set insert_Nil list.exhaust_sel set_append split_list_precedes)
    with wf have "reachable (hd sfx) ny"
      by (auto simp: wf_env_def is_subscc_def)
    from sfx wf have "reachable w (hd sfx)"
      by (auto simp: wf_env_def is_subscc_def)

    from \<open>reachable x nx\<close> \<open>reachable nx (hd (stack e))\<close>
         \<open>reachable (hd (stack e)) v\<close> \<open>reachable v w\<close>
         \<open>reachable w (hd sfx)\<close> \<open>reachable (hd sfx) ny\<close> \<open>reachable ny y\<close>
    show "reachable x y"
      using reachable_trans by meson
  qed

  have e': "e' = e\<lparr>\<S> := \<lambda>x. if x \<in> cc then cc else \<S> e x, stack := sfx\<rparr>"
    using unite_def e'_def cc_def pfx_def sfx_def by auto

  from pfx have hd_sfx: "\<S> e' (hd sfx) = cc"
    by (simp add: e')

  from tl_sfx_not_in_cc tl_int_cc
  have tl_sfx: "\<forall>x \<in> set (tl sfx). \<S> e' x = \<S> e x \<and> \<S> e' x \<inter> cc = {}"
    by (simp add: e')

  from sfx have "stack e' = (hd sfx) # tl sfx"
    by (auto simp: e')
  moreover
  from tl_sfx_not_in_cc have "\<forall>v \<in> set (tl sfx). \<S> e' v = \<S> e v"
    by (simp add: e')
  ultimately
  have "(\<Union> {\<S> e' v | v. v \<in> set (stack e')}) 
        = cc \<union> (\<Union> {\<S> e v | v. v \<in> set (tl sfx)})"
    using hd_sfx by auto
  moreover
  from \<open>stack e = pfx @ sfx\<close> sfx
  have "stack e = pfx @ (hd sfx # tl sfx)"
    by auto
  ultimately
  have s_equal: "(\<Union> {\<S> e' v | v. v \<in> set (stack e')}) 
               = (\<Union> {\<S> e v | v. v \<in> set (stack e)})"
    by (auto simp: cc_def)

  have "\<forall> x. \<S> e x \<subseteq> \<S> e' x"
  proof
    fix x
    show "\<S> e x \<subseteq> \<S> e' x"
    proof (cases "x \<in> cc")
      case True
      then obtain n where
        n: "n \<in> set pfx \<union> {hd sfx}" "x \<in> \<S> e n"
        by (auto simp: cc_def)
      with wf have "\<S> e x = \<S> e n"
        by (auto simp: wf_env_def)
      with \<open>n \<in> set pfx \<union> {hd sfx}\<close> have "\<S> e x \<subseteq> cc"
        by (auto simp: cc_def)
      moreover
      from n have "x \<in> cc"
        by (auto simp: cc_def)
      ultimately show ?thesis
        by (simp add: e')
    next
      case False
      then show ?thesis
        by (simp add: e')
    qed
  qed
  with s_equal show ?thesis
    by (simp add: sub_env_def e')
qed


text \<open>
  Similarly, we now show that the pre-conditions of the different
  function calls in the body of function @{text dfss} are satisfied.
  First, it is very easy to see that the pre-condition of @{text dfs}
  holds at the call of that function.
\<close>
lemma pre_dfss_pre_dfs:
  assumes "pre_dfss v e" and "w \<notin> visited e" and "w \<in> successors v"
  shows "pre_dfs w e" 
  using assms unfolding pre_dfss_def pre_dfs_def wf_env_def
  by (meson succ_reachable)

text \<open>
  The pre-condition of @{text dfss} holds when the successor
  considered in the current iteration has already been explored.
\<close>
lemma pre_dfss_pre_dfss_explored:
  fixes e v w
  defines "e'' \<equiv> e\<lparr>vsuccs := (\<lambda>x. if x=v then vsuccs e v \<union> {w} else vsuccs e x)\<rparr>"
  assumes 1: "pre_dfss v e" and 2: "w \<in> successors v" and 3: "w \<in> explored e"
  shows "pre_dfss v e''"
proof -
  from 1 have "v \<in> visited e"
    by (simp add: pre_dfss_def)
  have "wf_env e''"
  proof -
    from 1 have wf: "wf_env e"
      by (simp add: pre_dfss_def)
    hence "distinct (stack e'')"
          "\<forall>v \<in> visited e''. reachable (root e'') v"
          "set (stack e'') \<subseteq> visited e''"
          "explored e'' \<subseteq> visited e''"
          "explored e'' \<inter> set (stack e'') = {}"
          "\<forall>v w. w \<in> \<S> e'' v \<longleftrightarrow> (\<S> e'' v = \<S> e'' w)"
          "\<forall>v \<in> set (stack e''). \<forall> w \<in> set (stack e''). 
                v \<noteq> w \<longrightarrow> \<S> e'' v \<inter> \<S> e'' w = {}"
          "\<forall> v. v \<notin> visited e'' \<longrightarrow> \<S> e'' v = {v}"
          "\<Union> {\<S> e'' v | v. v \<in> set (stack e'')} = visited e'' - explored e''"
          "\<forall>x y. x \<preceq> y in stack e'' \<longrightarrow> reachable y x"
          "\<forall>x. is_subscc (\<S> e'' x)"
          "\<forall> x \<in> explored e''. \<forall> y. reachable x y \<longrightarrow> y \<in> explored e''"
          "\<forall> S \<in> sccs e''. is_scc S"
          "\<Union> (sccs e'') = explored e''"
      by (auto simp: wf_env_def e''_def)
    moreover
    from wf 2 have "\<forall>v. vsuccs e'' v \<subseteq> successors v"
      by (auto simp: wf_env_def e''_def)
    moreover 
    from wf 3 have "\<forall>v. vsuccs e'' v \<subseteq> visited e''"
      by (auto simp: wf_env_def e''_def)
    moreover
    from wf \<open>v \<in> visited e\<close>
    have "\<forall>v. v \<notin> visited e'' \<longrightarrow> vsuccs e'' v = {}"
      by (auto simp: wf_env_def e''_def)
    moreover
    from wf 2
    have "\<forall>v. v \<in> explored e'' \<longrightarrow> vsuccs e'' v = successors v"
      by (auto simp: wf_env_def e''_def)
    moreover
    have "\<forall>x y. x \<preceq> y in stack e'' \<and> x \<noteq> y \<longrightarrow>
             (\<forall>u \<in> \<S> e'' x. \<not> reachable_avoiding u y (unvisited e'' x))"
    proof (clarify)
      fix x y u
      assume "x \<preceq> y in stack e''" "x \<noteq> y" 
             "u \<in> \<S> e'' x"
             "reachable_avoiding u y (unvisited e'' x)"
      hence prec: "x \<preceq> y in stack e" "u \<in> \<S> e x"
        by (auto simp: e''_def)
      with wf have "y \<notin> explored e"
        unfolding wf_env_def by (metis Int_iff equals0D precedes_mem(2))
      have "(unvisited e x = unvisited e'' x)
          \<or> (unvisited e x = unvisited e'' x \<union> {(v,w)})"
        by (auto simp: e''_def unvisited_def split: if_splits)
      thus "False"
      proof
        assume "unvisited e x = unvisited e'' x"
        with prec \<open>x \<noteq> y\<close> \<open>reachable_avoiding u y (unvisited e'' x)\<close> wf
        show ?thesis
          unfolding wf_env_def by metis
      next
        assume "unvisited e x = unvisited e'' x \<union> {(v,w)}"
        with wf \<open>reachable_avoiding u y (unvisited e'' x)\<close>
             \<open>y \<notin> explored e\<close> \<open>w \<in> explored e\<close> prec \<open>x \<noteq> y\<close>
        show ?thesis
          using avoiding_explored[OF wf] unfolding wf_env_def
          by (metis (no_types, lifting))
      qed
    qed
    moreover 
    from wf
    have "distinct (cstack e'')"
         "set (cstack e'') \<subseteq> visited e''"
         "\<forall>n m. n \<preceq> m in stack e'' \<longrightarrow> n \<preceq> m in cstack e''"
         "\<forall>n \<in> set (stack e''). \<forall> m \<in> \<S> e'' n. m \<in> set (cstack e'') \<longrightarrow> m \<preceq> n in cstack e''"
      by (auto simp: e''_def wf_env_def)
    moreover 
    from wf 2
    have "\<forall>n \<in> visited e'' - set (cstack e''). vsuccs e'' n = successors n"
      by (auto simp: e''_def wf_env_def)
    ultimately show ?thesis
      unfolding wf_env_def by blast
  qed
  with 1 3 show ?thesis
    by (auto simp: pre_dfss_def e''_def)
qed

text \<open>
  The call to @{text dfs} establishes the pre-condition for the
  recursive call to @{text dfss} in the body of @{text dfss}.
\<close>
lemma pre_dfss_post_dfs_pre_dfss:
  fixes e v w
  defines "e' \<equiv> dfs w e"
  defines "e'' \<equiv> e'\<lparr>vsuccs := (\<lambda>x. if x=v then vsuccs e' v \<union> {w} else vsuccs e' x)\<rparr>"
  assumes pre: "pre_dfss v e"
      and w: "w \<in> successors v" "w \<notin> visited e"
      and post: "post_dfs w e e'"
  shows "pre_dfss v e''"
proof -
  from pre have "v \<in> visited e"
    by (simp add: pre_dfss_def)
  from post have "w \<in> visited e'"
    unfolding post_dfs_def wf_env_def by blast
  from pre post have "stack e' \<noteq> []"
    by (auto simp: pre_dfss_def post_dfs_def)
  have "v \<in> \<S> e' (hd (stack e'))"
  proof (cases "stack e' = stack e")
    case True
    with pre post show ?thesis
      unfolding pre_dfss_def post_dfs_def sub_env_def
      by (metis subsetD)
  next
    case False
    with post have se': "w \<in> \<S> e' (hd (stack e'))" "\<forall>n \<in> set (tl (stack e')). \<S> e' n = \<S> e n"
      by (auto simp: post_dfs_def)
    from pre have "hd (stack e) \<in> set (stack e)" "v \<in> \<S> e (hd (stack e))"
      by (auto simp: pre_dfss_def)
    with post obtain n where
      n: "n \<in> set (stack e')" "v \<in> \<S> e' n"
      unfolding post_dfs_def sub_env_def
      by (smt (verit, ccfv_threshold) Union_iff mem_Collect_eq subsetD)
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
      from \<open>n \<in> set (tl (stack e'))\<close> post \<open>stack e' \<noteq> []\<close> n 
      have "n \<in> set (tl (stack e))"
        unfolding post_dfs_def
        by (metis precedes_append_left precedes_refl self_append_conv2 tl_append2)
      from pre have "wf_env e" "stack e \<noteq> []" "v \<in> \<S> e (hd (stack e))"
        by (auto simp: pre_dfss_def)
      with \<open>n \<in> set (tl (stack e))\<close> \<open>v \<in> \<S> e n\<close> show ?thesis
        unfolding wf_env_def
        by (smt (verit, best) IntI Int_Diff Int_subset_iff UnionI distinct.simps(2) empty_iff empty_subsetI equalityD2 equalityI list.exhaust_sel list.set_sel(1) list.set_sel(2) mem_Collect_eq)
    qed
  qed

  have "wf_env e''"
  proof -
    from post have wf': "wf_env e'"
      by (simp add: post_dfs_def)
    hence "distinct (stack e'')"
          "\<forall>v \<in> visited e''. reachable (root e'') v"
          "set (stack e'') \<subseteq> visited e''"
          "explored e'' \<subseteq> visited e''"
          "explored e'' \<inter> set (stack e'') = {}"
          "\<forall>v w. w \<in> \<S> e'' v \<longleftrightarrow> (\<S> e'' v = \<S> e'' w)"
          "\<forall>v \<in> set (stack e''). \<forall> w \<in> set (stack e''). 
              v \<noteq> w \<longrightarrow> \<S> e'' v \<inter> \<S> e'' w = {}"
          "\<forall> v. v \<notin> visited e'' \<longrightarrow> \<S> e'' v = {v}"
          "\<Union> {\<S> e'' v | v. v \<in> set (stack e'')} = visited e'' - explored e''"
          "\<forall>x y. x \<preceq> y in stack e'' \<longrightarrow> reachable y x"
          "\<forall>x. is_subscc (\<S> e'' x)"
          "\<forall> x \<in> explored e''. \<forall> y. reachable x y \<longrightarrow> y \<in> explored e''"
          "\<forall> S \<in> sccs e''. is_scc S"
          "\<Union> (sccs e'') = explored e''"
      by (auto simp: wf_env_def e''_def)
    moreover
    from wf' w have "\<forall>v. vsuccs e'' v \<subseteq> successors v"
      by (auto simp: wf_env_def e''_def)
    moreover 
    from wf' \<open>w \<in> visited e'\<close> have "\<forall>v. vsuccs e'' v \<subseteq> visited e''"
      by (auto simp: wf_env_def e''_def)
    moreover
    have "\<forall>u. u \<notin> visited e'' \<longrightarrow> vsuccs e'' u = {}"
    proof (clarify)
      fix u
      assume u: "u \<notin> visited e''"
      with \<open>v \<in> visited e\<close> post have "u \<noteq> v"
        by (auto simp: post_dfs_def sub_env_def e''_def)
      moreover
      from u wf' have "vsuccs e' u = {}"
        by (auto simp: wf_env_def e''_def)
      ultimately show "vsuccs e'' u = {}"
        by (simp add: e''_def)
    qed
    moreover
    from wf' w
    have "\<forall>v. v \<in> explored e'' \<longrightarrow> vsuccs e'' v = successors v"
      by (auto simp: wf_env_def e''_def)
    moreover
    have "\<forall>x y. x \<preceq> y in stack e'' \<and> x \<noteq> y \<longrightarrow>
             (\<forall>u \<in> \<S> e'' x. \<not> reachable_avoiding u y (unvisited e'' x))"
    proof (clarify)
      fix x y u
      assume "x \<preceq> y in stack e''" "x \<noteq> y"
             "u \<in> \<S> e'' x"
             "reachable_avoiding u y (unvisited e'' x)"
      hence 1: "x \<preceq> y in stack e'" "u \<in> \<S> e' x"
        by (auto simp: e''_def)
      with wf' have "y \<notin> explored e'"
        unfolding wf_env_def by (metis Int_iff equals0D precedes_mem(2))
      have "(unvisited e' x = unvisited e'' x)
          \<or> (unvisited e' x = unvisited e'' x \<union> {(v,w)})"
        by (auto simp: e''_def unvisited_def split: if_splits)
      thus "False"
      proof
        assume "unvisited e' x = unvisited e'' x"
        with 1 \<open>x \<noteq> y\<close> \<open>reachable_avoiding u y (unvisited e'' x)\<close> wf'
        show ?thesis
          unfolding wf_env_def by metis
      next
        assume unv: "unvisited e' x = unvisited e'' x \<union> {(v,w)}"
        from post
        have "w \<in> explored e' 
           \<or> (w \<in> \<S> e' (hd (stack e')) \<and> (\<forall>n \<in> set (tl (stack e')). \<S> e' n = \<S> e n))"
          by (auto simp: post_dfs_def)
        thus ?thesis
        proof
          assume "w \<in> explored e'"
          with wf' unv \<open>reachable_avoiding u y (unvisited e'' x)\<close>
               \<open>y \<notin> explored e'\<close> 1 \<open>x \<noteq> y\<close>
          show ?thesis
            using avoiding_explored[OF wf'] unfolding wf_env_def
            by (metis (no_types, lifting))
        next
          assume w: "w \<in> \<S> e' (hd (stack e'))
                  \<and> (\<forall>n \<in> set (tl (stack e')). \<S> e' n = \<S> e n)"
          from \<open>reachable_avoiding u y (unvisited e'' x)\<close>[THEN ra_add_edge]
               unv
          have "reachable_avoiding u y (unvisited e' x)
              \<or> reachable_avoiding w y (unvisited e' x)"
            by auto
          thus ?thesis
          proof
            assume "reachable_avoiding u y (unvisited e' x)"
            with \<open>x \<preceq> y in stack e''\<close> \<open>x \<noteq> y\<close> \<open>u \<in> \<S> e'' x\<close> wf'
            show ?thesis
              by (auto simp: e''_def wf_env_def)
          next
            assume "reachable_avoiding w y (unvisited e' x)"
            from unv have "v \<in> \<S> e' x"
              by (auto simp: unvisited_def)
            from \<open>x \<preceq> y in stack e''\<close> have "x \<in> set (stack e')"
              by (simp add: e''_def precedes_mem)
            have "x = hd (stack e')"
            proof (rule ccontr)
              assume "x \<noteq> hd (stack e')"
              with \<open>x \<in> set (stack e')\<close> \<open>stack e' \<noteq> []\<close>
              have "x \<in> set (tl (stack e'))"
                by (metis hd_Cons_tl set_ConsD)
              with w \<open>v \<in> \<S> e' x\<close> have "v \<in> \<S> e x"
                by auto
              moreover
              from post \<open>stack e' \<noteq> []\<close> \<open>x \<in> set (stack e')\<close> \<open>x \<in> set (tl (stack e'))\<close>
              have "x \<in> set (tl (stack e))"
                unfolding post_dfs_def
                by (metis Un_iff self_append_conv2 set_append tl_append2)
              moreover
              from pre have "wf_env e" "stack e \<noteq> []" "v \<in> \<S> e (hd (stack e))"
                by (auto simp: pre_dfss_def)
              ultimately show "False"
                unfolding wf_env_def
                by (metis (no_types, lifting) distinct.simps(2) hd_Cons_tl insert_disjoint(2) list.set_sel(1) list.set_sel(2) mk_disjoint_insert)
            qed
            with \<open>reachable_avoiding w y (unvisited e' x)\<close>
                 \<open>x \<preceq> y in stack e''\<close> \<open>x \<noteq> y\<close> w wf'
            show ?thesis
              by (auto simp add: e''_def wf_env_def)
          qed
        qed
      qed
    qed

    moreover
    from wf'
    have "distinct (cstack e'')"
         "set (cstack e'') \<subseteq> visited e''"
         "\<forall>n m. n \<preceq> m in stack e'' \<longrightarrow> n \<preceq> m in cstack e''"
         "\<forall>n \<in> set (stack e''). \<forall> m \<in> \<S> e'' n. m \<in> set (cstack e'') \<longrightarrow> m \<preceq> n in cstack e''"
      by (auto simp: wf_env_def e''_def)
    moreover
    from wf' \<open>\<forall>v. vsuccs e'' v \<subseteq> successors v\<close>
    have "\<forall>n \<in> visited e'' - set (cstack e''). vsuccs e'' n = successors n"
      by (auto simp: wf_env_def e''_def split: if_splits)
    ultimately show ?thesis
    unfolding wf_env_def by blast
  qed

  show "pre_dfss v e''"
  proof -
    from pre post
    have "v \<in> visited e''"
      by (auto simp: pre_dfss_def post_dfs_def sub_env_def e''_def)
    moreover
    {
      fix u
      assume u: "u \<in> vsuccs e'' v"
      have "u \<in> explored e'' \<union> \<S> e'' (hd (stack e''))"
      proof (cases "u = w")
        case True
        with post show ?thesis
          by (auto simp: post_dfs_def e''_def)
      next
        case False
        with u pre post
        have "u \<in> explored e \<union> \<S> e (hd (stack e))"
          by (auto simp: pre_dfss_def post_dfs_def e''_def)
        then show ?thesis
        proof
          assume "u \<in> explored e"
          with post show ?thesis
            by (auto simp: post_dfs_def sub_env_def e''_def)
        next
          assume "u \<in> \<S> e (hd (stack e))"
          from pre have "hd (stack e) \<in> set (stack e)"
            by (auto simp: pre_dfss_def)
          with \<open>u \<in> \<S> e (hd (stack e))\<close>
          have "u \<in> \<Union> {\<S> e v | v . v \<in> set (stack e)}"
            by auto
          with post obtain n where
            n: "n \<in> set (stack e')" "u \<in> \<S> e' n"
            unfolding post_dfs_def sub_env_def
            by (smt (verit, ccfv_threshold) Union_iff mem_Collect_eq subsetD)
          have "n = hd (stack e')"
          proof (rule ccontr)
            assume "n \<noteq> hd (stack e')"
            with n \<open>stack e' \<noteq> []\<close> post
            have "n \<in> set (tl (stack e)) \<and> \<S> e' n = \<S> e n"
              unfolding post_dfs_def
              by (metis Un_iff list.exhaust_sel self_append_conv2 set_ConsD set_append tl_append2)
            with pre \<open>u \<in> \<S> e (hd (stack e))\<close> \<open>u \<in> \<S> e' n\<close>
            show "False"
              unfolding pre_dfss_def wf_env_def
              by (metis (no_types, lifting) distinct.simps(2) insert_Diff insert_disjoint(2) list.exhaust_sel list.set_sel(1) list.set_sel(2))
          qed
          with n show ?thesis
            by (simp add: e''_def)
        qed
      qed
    }
    moreover
    from pre post
    have "\<forall>n \<in> set (stack e''). reachable n v"
      unfolding pre_dfss_def post_dfs_def
      using e''_def by force
    moreover
    from \<open>stack e' \<noteq> []\<close> have "stack e'' \<noteq> []"
      by (simp add: e''_def)
    moreover
    from \<open>v \<in> \<S> e' (hd (stack e'))\<close> have "v \<in> \<S> e'' (hd (stack e''))"
      by (simp add: e''_def)
    moreover
    from pre post have "\<exists>ns. cstack e'' = v # ns"
      by (auto simp: pre_dfss_def post_dfs_def e''_def)
    ultimately show ?thesis
      using \<open>wf_env e''\<close> unfolding pre_dfss_def by blast
  qed
qed

text \<open>
  Finally, the pre-condition for the recursive call to @{text dfss}
  at the end of the body of function @{text dfss} also holds if
  @{text unite} was applied.
\<close>

lemma pre_dfss_unite_pre_dfss:
  fixes e v w
  defines "e' \<equiv> unite v w e"
  defines "e'' \<equiv> e'\<lparr>vsuccs := (\<lambda>x. if x=v then vsuccs e' v \<union> {w} else vsuccs e' x)\<rparr>"
  assumes pre: "pre_dfss v e"
      and w: "w \<in> successors v" "w \<notin> vsuccs e v" "w \<in> visited e" "w \<notin> explored e"
  shows "pre_dfss v e''"
proof -
  from pre have wf: "wf_env e"
    by (simp add: pre_dfss_def)
  from pre have "v \<in> visited e"
    by (simp add: pre_dfss_def)
  from pre w have "v \<notin> explored e"
    unfolding pre_dfss_def wf_env_def
    by (meson reachable_edge)

  define pfx where "pfx = takeWhile (\<lambda>x. w \<notin> \<S> e x) (stack e)"
  define sfx where "sfx = dropWhile (\<lambda>x. w \<notin> \<S> e x) (stack e)"
  define cc where "cc = \<Union> {\<S> e x |x. x \<in> set pfx \<union> {hd sfx}}"

  have "stack e = pfx @ sfx"
    by (simp add: pfx_def sfx_def)

  have cc_Un: "cc = \<Union> {\<S> e x | x. x \<in> cc}"
  proof
    {
      fix n
      assume "n \<in> cc"
      with wf have "n \<in> \<Union> {\<S> e x | x. x \<in> cc}"
        unfolding wf_env_def cc_def
        by (smt (verit, ccfv_threshold) Union_iff mem_Collect_eq)
    }
    thus "cc \<subseteq> \<Union> {\<S> e x | x. x \<in> cc}" ..
  next
    {
      fix n x
      assume "x \<in> cc" "n \<in> \<S> e x"
      with \<open>wf_env e\<close> have "n \<in> cc"
        unfolding wf_env_def cc_def
        by (smt (verit) Union_iff mem_Collect_eq)
    }
    thus "(\<Union> {\<S> e x | x. x \<in> cc}) \<subseteq> cc"
      by blast
  qed

  from wf w have "w \<in> \<Union> {\<S> e n | n. n \<in> set (stack e)}"
    by (simp add: wf_env_def)
  then obtain n where "n \<in> set (stack e)" "w \<in> \<S> e n"
    by auto
  hence sfx: "sfx \<noteq> [] \<and> w \<in> \<S> e (hd sfx)"
    unfolding sfx_def
    by (metis dropWhile_eq_Nil_conv hd_dropWhile)
  with \<open>wf_env e\<close> \<open>stack e = pfx @ sfx\<close> 
  have pfx: "set pfx \<union> {hd sfx} \<subseteq> cc"
    unfolding wf_env_def cc_def 
    by (smt (verit) Union_iff mem_Collect_eq subset_eq)

  from pre \<open>stack e = pfx @ sfx\<close> sfx
  have "v \<in> cc"
    unfolding pre_dfss_def cc_def
    by (smt (verit, ccfv_threshold) Un_iff UnionI hd_append2 insert_iff list.set_sel(1) mem_Collect_eq self_append_conv2)

  have tl_int_cc: "\<forall>n \<in> set (tl sfx). \<S> e n \<inter> cc = {}"
  proof -
    {
      fix n u
      assume "n \<in> set (tl sfx)" "u \<in> \<S> e n" "u \<in> cc"
      from sfx \<open>n \<in> set (tl sfx)\<close> \<open>stack e = pfx @ sfx\<close> wf
      have n: "n \<in> set (stack e) - (set pfx \<union> {hd sfx})"
        unfolding wf_env_def
        by (metis Diff_iff Int_iff Un_iff distinct.simps(2) distinct_append empty_iff list.exhaust_sel list.set_sel(2) set_append singletonD)
      from \<open>u \<in> cc\<close> obtain n' where
        n': "n' \<in> set pfx \<union> {hd sfx}" "u \<in> \<S> e n'"
        by (auto simp: cc_def)
      with n \<open>stack e = pfx @ sfx\<close> sfx wf
      have "\<S> e n \<inter> \<S> e n' = {}"
        unfolding wf_env_def
        by (metis (no_types, lifting) DiffE UnCI UnE list.set_sel(1) set_append singleton_iff)
      with \<open>u \<in> \<S> e n\<close> \<open>u \<in> \<S> e n'\<close> have "False"
        by auto
    }
    thus ?thesis by auto
  qed

  with wf sfx \<open>stack e = pfx @ sfx\<close>
  have tl_sfx_not_in_cc: "\<forall>x \<in> set (tl sfx). x \<notin> cc"
    unfolding wf_env_def cc_def
    by (metis (no_types, lifting) disjoint_insert(1) insert_Diff)

  have cc_scc: "is_subscc cc"
  proof (clarsimp simp: is_subscc_def)
    fix x y
    assume "x \<in> cc" "y \<in> cc"
    then obtain nx ny where
      nx: "nx \<in> set pfx \<union> {hd sfx}" "x \<in> \<S> e nx" and
      ny: "ny \<in> set pfx \<union> {hd sfx}" "y \<in> \<S> e ny"
      by (auto simp: cc_def)
    with wf have "reachable x nx" "reachable ny y"
      by (auto simp: wf_env_def is_subscc_def)
    from w pre have "reachable v w"
      by (auto simp: pre_dfss_def)
    from pre have "reachable (hd (stack e)) v"
      by (auto simp: pre_dfss_def wf_env_def is_subscc_def)
    from pre have "stack e = hd (stack e) # tl (stack e)"
      by (auto simp: pre_dfss_def)
    with nx \<open>stack e = pfx @ sfx\<close> sfx
    have "hd (stack e) \<preceq> nx in stack e"
      by (metis Un_iff Un_insert_right head_precedes list.exhaust_sel list.simps(15) set_append sup_bot.right_neutral)
    with wf have "reachable nx (hd (stack e))"
      by (auto simp: wf_env_def)
    from \<open>stack e = pfx @ sfx\<close> sfx ny
    have "ny \<preceq> hd sfx in stack e" 
      by (metis List.set_insert empty_set insert_Nil list.exhaust_sel set_append split_list_precedes)
    with wf have "reachable (hd sfx) ny"
      by (auto simp: wf_env_def is_subscc_def)
    from sfx wf have "reachable w (hd sfx)"
      by (auto simp: wf_env_def is_subscc_def)

    from \<open>reachable x nx\<close> \<open>reachable nx (hd (stack e))\<close>
         \<open>reachable (hd (stack e)) v\<close> \<open>reachable v w\<close>
         \<open>reachable w (hd sfx)\<close> \<open>reachable (hd sfx) ny\<close> \<open>reachable ny y\<close>
    show "reachable x y"
      using reachable_trans by meson
  qed

  have e': "e' = e\<lparr>\<S> := \<lambda>x. if x \<in> cc then cc else \<S> e x, stack := sfx\<rparr>"
    using unite_def e'_def cc_def pfx_def sfx_def by auto

  from pfx have hd_sfx: "\<S> e' (hd sfx) = cc"
    by (simp add: e')

  from tl_sfx_not_in_cc tl_int_cc
  have tl_sfx: "\<forall>x \<in> set (tl sfx). \<S> e' x = \<S> e x \<and> \<S> e' x \<inter> cc = {}"
    by (simp add: e')

  from sfx have "stack e' = (hd sfx) # tl sfx"
    by (auto simp: e')
  moreover
  from tl_sfx_not_in_cc have "\<forall>v \<in> set (tl sfx). \<S> e' v = \<S> e v"
    by (simp add: e')
  ultimately
  have "(\<Union> {\<S> e' v | v. v \<in> set (stack e')}) 
        = cc \<union> (\<Union> {\<S> e v | v. v \<in> set (tl sfx)})"
    using hd_sfx by auto
  moreover
  from \<open>stack e = pfx @ sfx\<close> sfx
  have "stack e = pfx @ (hd sfx # tl sfx)"
    by auto
  ultimately
  have s_equal: "(\<Union> {\<S> e' v | v. v \<in> set (stack e')}) 
               = (\<Union> {\<S> e v | v. v \<in> set (stack e)})"
    by (auto simp: cc_def)

  moreover have "sub_env e e'"
    using unite_mono
    by (simp add: e'_def pre w)

  have "wf_env e''"
  proof -
    from wf \<open>stack e = pfx @ sfx\<close>
    have "distinct (stack e'')" 
         "\<forall>v \<in> visited e''. reachable (root e'') v"
         "set (stack e'') \<subseteq> visited e''" 
         "explored e'' \<subseteq> visited e''"
         "explored e'' \<inter> set (stack e'') = {}"
         "\<forall>S \<in> sccs e''. is_scc S"
         "\<Union> (sccs e'') = explored e''"
         "distinct (cstack e'')"
         "set (cstack e'') \<subseteq> visited e''"
      by (auto simp: wf_env_def e' e''_def)

    moreover
    from wf w have "\<forall>x. vsuccs e'' x \<subseteq> successors x"
      by (simp add: wf_env_def e' e''_def)

    moreover
    from wf \<open>w \<in> visited e\<close> have "\<forall>x. vsuccs e'' x \<subseteq> visited e''"
      by (simp add: wf_env_def e' e''_def)

    moreover
    from wf \<open>w \<in> visited e\<close> \<open>v \<in> visited e\<close>
    have "\<forall>x. x \<notin> visited e'' \<longrightarrow> vsuccs e'' x = {}"
      by (simp add: wf_env_def e' e''_def)

    moreover
    from wf \<open>v \<notin> explored e\<close>
    have "\<forall>x. x \<in> explored e'' \<longrightarrow> vsuccs e'' x = successors x"
      by (simp add: wf_env_def e' e''_def)

    moreover
    {
      fix x y
      have "y \<in> \<S> e' x \<longleftrightarrow> (\<S> e' x = \<S> e' y)"
      proof
        assume y: "y \<in> \<S> e' x"
        show "\<S> e' x = \<S> e' y"
        proof (cases "x \<in> cc")
          case True
          with y show ?thesis
            by (simp add: e')
        next
          case False
          with y \<open>wf_env e\<close> have "\<S> e x = \<S> e y"
            by (simp add: wf_env_def e')
          with False cc_Un \<open>wf_env e\<close> have "y \<notin> cc"
            unfolding wf_env_def e'_def
            by (smt (verit, best) Union_iff mem_Collect_eq)
          with \<open>\<S> e x = \<S> e y\<close> False show ?thesis
            by (simp add: e')
        qed
      next
        assume sx: "\<S> e' x = \<S> e' y"
        show "y \<in> \<S> e' x"
        proof (cases "x \<in> cc")
          case True
          hence "\<S> e' x = cc"
            by (simp add: e')
          moreover have "y \<in> cc"
          proof (rule ccontr)
            assume y: "y \<notin> cc"
            with \<open>\<S> e' x = cc\<close> sx have "\<S> e y = cc"
              by (simp add: e')
            with wf have "y \<in> cc"
              unfolding wf_env_def by metis
            with y show "False" ..
          qed
          ultimately show ?thesis 
            by simp
        next
          case False
          hence "\<S> e' x = \<S> e x"
            by (simp add: e')
          have "y \<notin> cc"
          proof
            assume y: "y \<in> cc"
            with \<open>\<S> e' x = \<S> e x\<close> sx have "\<S> e x = cc"
              by (simp add: e')
            with wf have "x \<in> cc"
              unfolding wf_env_def by metis
            with \<open>x \<notin> cc\<close> show "False" ..
          qed
          with sx \<open>\<S> e' x = \<S> e x\<close> have "\<S> e y = \<S> e x"
            by (simp add: e')
          with wf have "y \<in> \<S> e x"
            unfolding wf_env_def by metis
          with \<open>\<S> e' x = \<S> e x\<close> show ?thesis
            by simp
        qed
      qed
      hence "y \<in> \<S> e'' x \<longleftrightarrow> (\<S> e'' x = \<S> e'' y)"
        by (simp add: e''_def)
    }

    moreover
    have "\<forall>x \<in> set (stack e''). \<forall>y \<in> set (stack e'').
             x \<noteq> y \<longrightarrow> \<S> e'' x \<inter> \<S> e'' y = {}"
    proof (clarify)
      fix x y
      assume "x \<in> set (stack e'')" "y \<in> set (stack e'')" "x \<noteq> y"
      hence xy: "x \<in> set sfx" "y \<in> set sfx"
        by (auto simp: e' e''_def)
      show "\<S> e'' x \<inter> \<S> e'' y = {}"
      proof (cases "x = hd sfx")
        case True
        with xy \<open>x \<noteq> y\<close> sfx have "y \<in> set (tl sfx)"
          by (metis list.exhaust_sel set_ConsD)
        with True hd_sfx tl_sfx show ?thesis
          by (auto simp: e''_def)
      next
        case False
        with xy sfx have "x \<in> set (tl sfx)"
          by (metis list.exhaust_sel set_ConsD)
        show ?thesis
        proof (cases "y = hd sfx")
          case True
          with \<open>x \<in> set (tl sfx)\<close> hd_sfx tl_sfx show ?thesis
            by (auto simp: e''_def)
        next
          case False
          with xy sfx have "y \<in> set (tl sfx)"
            by (metis list.exhaust_sel set_ConsD)
          with \<open>x \<in> set (tl sfx)\<close> tl_sfx
          have "\<S> e'' x = \<S> e x \<and> \<S> e'' y = \<S> e y"
            by (auto simp: e''_def)
          with xy \<open>stack e = pfx @ sfx\<close> \<open>x \<noteq> y\<close> wf show ?thesis
            by (auto simp: wf_env_def)
        qed
      qed
    qed

    moreover
    have "\<forall>x. x \<notin> visited e'' \<longrightarrow> \<S> e'' x = {x}"
    proof (clarify)
      fix x
      assume "x \<notin> visited e''"
      hence "x \<notin> visited e"
        by (simp add: e' e''_def)
      moreover have "x \<notin> cc"
      proof
        assume "x \<in> cc"
        then obtain n where "n \<in> set pfx \<union> {hd sfx}" "x \<in> \<S> e n"
          by (auto simp: cc_def)
        with \<open>stack e = pfx @ sfx\<close> sfx wf \<open>x \<notin> visited e\<close>
        show "False"
          unfolding wf_env_def
          by (metis Un_iff list.set_sel(1) set_append singletonD subsetD)
      qed
      ultimately show "\<S> e'' x = {x}"
        using wf by (auto simp: wf_env_def e' e''_def)
    qed

    moreover
    from s_equal wf
    have "\<Union> {\<S> e'' x | x. x \<in> set (stack e'')} = visited e'' - explored e''"
      by (auto simp: wf_env_def e' e''_def)

    moreover
    have "\<forall>x y. x \<preceq> y in stack e'' \<longrightarrow> reachable y x"
    proof (clarify)
      fix x y
      assume "x \<preceq> y in stack e''"
      hence "x \<preceq> y in sfx"
        by (simp add: e' e''_def)
      with \<open>stack e = pfx @ sfx\<close> wf
      show "reachable y x"
        unfolding wf_env_def by (metis precedes_append_left)
    qed

    moreover
    from cc_scc wf have "\<forall>x. is_subscc (\<S> e'' x)"
      by (auto simp: e''_def e' wf_env_def)

    moreover
    from wf have "\<forall>x \<in> explored e''. \<forall>y. reachable x y \<longrightarrow> y \<in> explored e''"
      by (auto simp: e''_def e' wf_env_def)

    moreover
    have "\<forall>x y. x \<preceq> y in stack e'' \<and> x \<noteq> y \<longrightarrow>
                (\<forall>u \<in> \<S> e'' x. \<not> reachable_avoiding u y (unvisited e'' x))"
    proof (clarify)
      fix x y u
      assume xy: "x \<preceq> y in stack e''" "x \<noteq> y"
         and u: "u \<in> \<S> e'' x" "reachable_avoiding u y (unvisited e'' x)"
      show "False"
      proof (cases "x = hd (stack e'')")
        case True
        with hd_sfx have "\<S> e'' x = cc" 
          by (simp add: e''_def e')
        with \<open>u \<in> \<S> e'' x\<close> obtain x' where
          x': "x' \<in> set pfx \<union> {hd sfx}" "u \<in> \<S> e x'"
          by (auto simp: cc_def)
        with \<open>stack e = pfx @ (hd sfx # tl sfx)\<close> True
        have "x' \<preceq> x in stack e"
          by (simp add: e''_def e' split_list_precedes)
        moreover
        from xy \<open>stack e = pfx @ sfx\<close> have "x \<preceq> y in stack e"
          by (simp add: e''_def e' precedes_append_left)
        ultimately have "x' \<preceq> y in stack e"
          using wf by (auto simp: wf_env_def elim: precedes_trans)
        from \<open>x' \<preceq> x in stack e\<close> \<open>x \<preceq> y in stack e\<close> wf \<open>x \<noteq> y\<close>
        have "x' \<noteq> y"
          by (auto simp: wf_env_def dest: precedes_antisym)
        let ?unv = "\<Union> {unvisited e y | y. y \<in> set pfx \<union> {hd sfx}}"
        have "?unv \<subseteq> unvisited e'' x \<union> {(v,w)}"
        proof
          fix u
          assume "u \<in> ?unv"
          then obtain y a b where
            "y \<in> set pfx \<union> {hd sfx}" "u = (a,b)"
            "a \<in> \<S> e y" "b \<in> successors a - vsuccs e a"
            by (auto simp: unvisited_def)
          with \<open>\<S> e'' x = cc\<close> have "a \<in> \<S> e'' x"
            by (auto simp: cc_def)
          moreover
          from \<open>b \<in> successors a - vsuccs e a\<close>
          have "(b \<in> successors a - vsuccs e'' a) \<or> (a=v \<and> b=w)"
            by (auto simp: e''_def e')
          ultimately
          show "u \<in> unvisited e'' x \<union> {(v,w)}"
            using \<open>u = (a,b)\<close> by (auto simp: unvisited_def)
        qed
        moreover
        have "unvisited e'' x \<subseteq> ?unv"
        proof
          fix u
          assume "u \<in> unvisited e'' x"
          then obtain a b where
            ab: "a \<in> \<S> e'' x" "b \<in> successors a - vsuccs e'' a" "u = (a,b)"
            by (auto simp: unvisited_def)
          with \<open>\<S> e'' x = cc\<close> obtain y where
            "y \<in> set pfx \<union> {hd sfx}" "a \<in> \<S> e y"
            by (auto simp: cc_def)
          with ab show "u \<in> ?unv"
            by (auto simp: e''_def e' unvisited_def split: if_splits)
        qed
        moreover
        from \<open>v \<in> cc\<close> w have "(v,w) \<in> ?unv"
          by (auto simp: cc_def unvisited_def)
        ultimately have "?unv = unvisited e'' x \<union> {(v,w)}"
          by blast
        with \<open>reachable_avoiding u y (unvisited e'' x)\<close>[THEN ra_add_edge]
        have "reachable_avoiding u y ?unv \<or> reachable_avoiding w y ?unv"
          by auto
        thus ?thesis
        proof
          assume "reachable_avoiding u y ?unv"
          with x' have "reachable_avoiding u y (unvisited e x')"
            by (blast intro: ra_mono)
          with \<open>x' \<preceq> y in stack e\<close> \<open>x' \<noteq> y\<close> \<open>u \<in> \<S> e x'\<close> wf
          show ?thesis
            by (auto simp: wf_env_def)
        next
          assume "reachable_avoiding w y ?unv"
          with sfx \<open>x = hd (stack e'')\<close>
          have "reachable_avoiding w y (unvisited e x)"
            by (auto simp: e''_def e' intro: ra_mono)
          moreover
          from sfx \<open>x = hd (stack e'')\<close> have "w \<in> \<S> e x"
            by (simp add: e''_def e')
          moreover
          from \<open>stack e = pfx @ sfx\<close> \<open>x \<preceq> y in stack e''\<close>
          have "x \<preceq> y in stack e"
            by (simp add: e''_def e' precedes_append_left)
          ultimately show ?thesis
            using \<open>x \<noteq> y\<close> wf by (auto simp: wf_env_def)
        qed
      next
        case False
        with \<open>x \<preceq> y in stack e''\<close> sfx
        have "x \<in> set (tl sfx)"
          apply (simp add: e''_def e')
          by (metis hd_Cons_tl precedes_mem(1) set_ConsD)
        with tl_sfx_not_in_cc \<open>u \<in> \<S> e'' x\<close> have "u \<in> \<S> e x"
          by (simp add: e''_def e')
        moreover
        from \<open>x \<preceq> y in stack e''\<close> \<open>stack e = pfx @ sfx\<close>
        have "x \<preceq> y in stack e"
          by (simp add: e''_def e' precedes_append_left)
        moreover
        from \<open>v \<in> cc\<close> \<open>x \<in> set (tl sfx)\<close> tl_int_cc tl_sfx_not_in_cc
        have "v \<notin> \<S> e'' x"
          by (auto simp: e''_def e')
        with \<open>x \<in> set (tl sfx)\<close> tl_sfx_not_in_cc
        have "unvisited e'' x = unvisited e x"
          by (auto simp: e''_def e' unvisited_def split: if_splits)
        ultimately show ?thesis
          using \<open>x \<noteq> y\<close> \<open>reachable_avoiding u y (unvisited e'' x)\<close> wf
          by (auto simp: wf_env_def)
      qed
    qed

    moreover
    from wf w
    have "\<forall>n \<in> visited e'' - set (cstack e''). vsuccs e'' n = successors n"
      by (auto simp: e''_def e' wf_env_def)

    moreover
    from wf \<open>stack e = pfx @ sfx\<close>
    have "\<forall>n m. n \<preceq> m in stack e'' \<longrightarrow> n \<preceq> m in cstack e''"
      apply (simp add: e''_def e')
      unfolding wf_env_def by (metis precedes_append_left)

    moreover
    have "\<forall>n \<in> set (stack e''). \<forall>m \<in> \<S> e'' n. m \<in> set (cstack e'') \<longrightarrow> m \<preceq> n in cstack e''"
    proof (clarsimp simp add: e''_def)
      fix n m
      assume "n \<in> set (stack e')" "m \<in> \<S> e' n" "m \<in> set (cstack e')"
      show "m \<preceq> n in cstack e'"
      proof (cases "n = hd (stack e')")
        case True
        hence "n = hd sfx"
          by (simp add: e')
        with \<open>m \<in> \<S> e' n\<close> hd_sfx obtain x where
          "x \<in> set pfx \<union> {hd sfx}" "m \<in> \<S> e x"
          by (auto simp: cc_def)
        with \<open>stack e = pfx @ sfx\<close> sfx \<open>m \<in> set (cstack e')\<close> wf
        have "m \<preceq> x in cstack e"
          by (auto simp: e' wf_env_def)
        moreover
        from \<open>x \<in> set pfx \<union> {hd sfx}\<close> \<open>n = hd sfx\<close> \<open>stack e = pfx @ (hd sfx # tl sfx)\<close>
        have "x \<preceq> n in stack e" 
          by (metis List.set_insert empty_set insert_Nil set_append split_list_precedes)
        with wf have "x \<preceq> n in cstack e" "distinct (cstack e)"
          by (auto simp: wf_env_def)
        ultimately show ?thesis
          by (auto simp: e' elim: precedes_trans)
      next
        case False
        with \<open>n \<in> set (stack e')\<close> \<open>stack e' = hd sfx # tl sfx\<close>
        have "n \<in> set (tl sfx)"
          by auto
        with tl_sfx_not_in_cc \<open>m \<in> \<S> e' n\<close> have "m \<in> \<S> e n"
          by (simp add: e')
        moreover
        from \<open>n \<in> set (stack e')\<close> \<open>stack e = pfx @ sfx\<close>
        have "n \<in> set (stack e)"
          by (auto simp: e')
        ultimately show ?thesis
          using \<open>m \<in> set (cstack e')\<close> wf
          by (auto simp: wf_env_def e')
      qed
    qed

    ultimately show ?thesis
      by (auto simp: wf_env_def)
  qed

  show "pre_dfss v e''"
  proof -
    from pre have "v \<in> visited e''"
      by (simp add: pre_dfss_def e' e''_def)

    moreover
    {
      fix u
      assume u: "u \<in> vsuccs e'' v"
      have "u \<in> explored e'' \<union> \<S> e'' (hd (stack e''))"
      proof (cases "u = w")
        case True
        with sfx show ?thesis 
          by (auto simp: e''_def e' cc_def)
      next
        case False
        with u have "u \<in> vsuccs e v"
          by (simp add: e''_def e')
        with pre have "u \<in> explored e \<union> \<S> e (hd (stack e))"
          by (auto simp: pre_dfss_def)
        then show ?thesis
        proof
          assume "u \<in> explored e"
          thus ?thesis
            by (simp add: e''_def e')
        next
          assume "u \<in> \<S> e (hd (stack e))"
          with \<open>stack e = pfx @ (hd sfx # tl sfx)\<close> have "u \<in> cc"
            unfolding cc_def
            by (smt (verit, ccfv_threshold) UnCI UnionI hd_append2 insertCI list.sel(1) list.set_sel(1) mem_Collect_eq self_append_conv2)
          with hd_sfx sfx show ?thesis
            by (auto simp: e''_def e')
        qed
      qed
    }
    hence "\<forall>w \<in> vsuccs e'' v. w \<in> explored e'' \<union> \<S> e'' (hd (stack e''))"
      by blast

    moreover
    from pre \<open>stack e = pfx @ sfx\<close>
    have "\<forall>n \<in> set (stack e''). reachable n v"
      by (auto simp: pre_dfss_def e''_def e')

    moreover
    from sfx have "stack e'' \<noteq> []"
      by (auto simp: e''_def e')

    moreover
    from \<open>v \<in> cc\<close> sfx hd_sfx have "v \<in> \<S> e'' (hd (stack e''))"
      by (auto simp: e''_def e')

    moreover
    from pre have "\<exists>ns. cstack e'' = v # ns"
      by (auto simp: pre_dfss_def e''_def e')

    ultimately show ?thesis
      using \<open>wf_env e''\<close> unfolding pre_dfss_def by blast
  qed
qed


text \<open>
  Assuming the pre-condition of function @{text dfs} and the post-condition of
  the call to @{text dfss} in the body of that function, the post-condition of
  @{text dfs} is established.
\<close>
lemma pre_dfs_implies_post_dfs:
  fixes v e
  defines "e1 \<equiv> e\<lparr>visited := visited e \<union> {v}, stack := (v # stack e), cstack:=(v # cstack e)\<rparr>"
  defines "e' \<equiv> dfss v e1"
  defines "e'' \<equiv> e'\<lparr> cstack := tl(cstack e')\<rparr>"
  assumes 1: "pre_dfs v e"
      and 2: "dfs_dfss_dom (Inl(v, e))"
      and 3: "post_dfss v e1 e'"
  shows "post_dfs v e (dfs v e)"
proof (cases "v = hd(stack e')")
  case True
  have notempty: "stack e' = v # stack e"
  proof -
    from 3 obtain ns where ns: "stack e1 = ns @ (stack e')" "stack e' \<noteq> []"
      by (auto simp: post_dfss_def)
    have "ns = []"
    proof (rule ccontr)
      assume "ns \<noteq> []"
      with ns have "hd(ns) = v"
        apply (simp add: e1_def)
        by (metis hd_append2 list.sel(1))
      hence "\<not> distinct (stack e1)" using True ns \<open>ns \<noteq> []\<close>
        by (metis disjoint_iff_not_equal distinct_append hd_in_set) 
      with 1 e1_def show False
        by (auto simp: pre_dfs_def wf_env_def)
    qed
    with ns show ?thesis
      by (simp add: e1_def)
  qed
  from 3 have "cstack e' = v # cstack e"
    by (auto simp: post_dfss_def e1_def)
  have e2:"dfs v e = e'\<lparr>sccs := sccs e' \<union> {\<S> e' v}, 
                        explored := explored e' \<union> (\<S> e' v), 
                        stack := tl (stack e'),
                        cstack := tl (cstack e')\<rparr>" (is "_ = ?e2")
    using True 2 dfs.psimps[of v e] unfolding e1_def e'_def 
    by (fastforce simp: e1_def e'_def)
  from 3 have "wf_env e'"
    by (simp add: post_dfss_def)
  have stack:"stack ?e2 = tl (stack e')" 
    by simp
  have Se'e2_eq:"\<forall> x. \<S> e' x = \<S> ?e2 x"
    by simp
  have sub: "sub_env e e1"
    by (auto simp: sub_env_def e1_def)

  from notempty have stack2: "stack ?e2 = stack e"
    by (simp add: e1_def)

  moreover from 3 have "v \<in> visited ?e2"
    by (auto simp: post_dfss_def sub_env_def e1_def)

  moreover have subenv: "sub_env e ?e2" 
  proof -
    from sub 3 have "sub_env e e'"
      unfolding post_dfss_def by (auto elim: sub_env_trans)

    moreover
    have "\<Union> {\<S> e n | n. n \<in> set (stack e)} \<subseteq> \<Union> {\<S> ?e2 n | n. n \<in> set (stack ?e2)}"
    proof -
      from stack2 Se'e2_eq
      have "\<Union> {\<S> ?e2 n | n. n \<in> set (stack ?e2)} = \<Union> {\<S> e' n | n. n \<in> set (stack e)}"
        by metis
      with \<open>sub_env e e'\<close> show ?thesis
        unfolding sub_env_def by fastforce
    qed

    ultimately show ?thesis
      by (auto simp: sub_env_def)
  qed

  moreover have "wf_env ?e2"
  proof -
    have "distinct (stack ?e2)"
      using \<open>wf_env e'\<close> by (auto simp: wf_env_def distinct_tl)

    moreover
    from \<open>wf_env e'\<close> have "\<forall>v \<in> visited ?e2. reachable (root ?e2) v"
      by (auto simp: wf_env_def)

    moreover 
    from notempty \<open>wf_env e'\<close> have "set (stack ?e2) \<subseteq> visited ?e2"
      by (auto simp: wf_env_def)
  
    moreover 
    from notempty \<open>wf_env e'\<close> have "explored ?e2 \<subseteq> visited ?e2"
      apply (simp add: wf_env_def)
      by (smt (verit) singletonD subset_eq)
  
    moreover 
    {
      fix w
      assume w1: "w \<in> explored ?e2" and w2: "w \<in> set (stack ?e2)"
      have "explored ?e2 = explored e' \<union> \<S> e' v" 
        by auto
      have False
      proof (cases "w \<in> explored e'")
        case True
        with w2 3 stack show ?thesis
          unfolding post_dfss_def wf_env_def
          by (metis IntI equals0D list.set_sel(2))
      next
        case False
        with w1 have "w \<in> \<S> e' v"
          by auto 
        from w2 have "w \<in> set (tl (stack e'))"
          by simp
        with \<open>wf_env e'\<close> notempty have "w \<noteq> v"
          by (auto simp: wf_env_def)
        with 3 \<open>w \<in> \<S> e' v\<close> \<open>w \<in> set (tl (stack e'))\<close> notempty
        show ?thesis
          unfolding post_dfss_def wf_env_def
          by (metis True is_subscc_def)
      qed
    }
    hence "explored ?e2 \<inter> set (stack ?e2) = {}"
      by blast

    moreover
    from \<open>wf_env e'\<close> 
    have "\<forall>v. vsuccs ?e2 v \<subseteq> successors v"
         "\<forall>v. vsuccs ?e2 v \<subseteq> visited ?e2"
         "\<forall>v. v \<notin> visited ?e2 \<longrightarrow> vsuccs ?e2 v = {}"
      by (auto simp: wf_env_def)

    moreover
    {
      fix u
      assume "u \<in> explored ?e2"
      have "vsuccs ?e2 u = successors u"
      proof (cases "u \<in> explored e'")
        case True
        with \<open>wf_env e'\<close> show ?thesis
          by (auto simp: wf_env_def)
      next
        case False
        with \<open>u \<in> explored ?e2\<close> have "u \<in> \<S> e' v"
          by simp
        have "vsuccs ?e2 u = vsuccs e' u"
          by simp
        show ?thesis
        proof (cases "u = v")
          case True
          with 3 show ?thesis
            by (auto simp: post_dfss_def)
        next
          case False
          from 3 have "cstack e' = v # cstack e"
            by (auto simp: post_dfss_def e1_def)
          have "u \<in> visited e' - set (cstack e')"
          proof
            from notempty \<open>u \<in> \<S> e' v\<close> \<open>wf_env e'\<close> False
            show "u \<in> visited e'"
              unfolding wf_env_def
              by (metis singletonD)
          next
            show "u \<notin> set (cstack e')"
            proof
              assume u: "u \<in> set (cstack e')"
              with notempty \<open>u \<in> \<S> e' v\<close> \<open>wf_env e'\<close> have "u \<preceq> v in cstack e'"
                by (auto simp: wf_env_def)
              with \<open>cstack e' = v # cstack e\<close> u False \<open>wf_env e'\<close> show "False"
                unfolding wf_env_def
                by (metis head_precedes precedes_antisym)
            qed
          qed
          with 3 show ?thesis
            by (auto simp: post_dfss_def wf_env_def)
        qed
      qed
    }
    note explored_vsuccs = this

    moreover
    from \<open>wf_env e'\<close> have "\<forall>v w. w \<in> \<S> ?e2 v \<longleftrightarrow> (\<S> ?e2 v = \<S> ?e2 w)"
      by (auto simp: wf_env_def)

    moreover
    from 3 Se'e2_eq stack
    have onStackOneRepr: "\<forall>v w. (v \<in> set (stack ?e2) \<and> w \<in> set (stack ?e2) \<and> v \<noteq> w) \<longrightarrow> (\<S> ?e2 v \<inter> \<S> ?e2 w = {})"
      unfolding post_dfss_def wf_env_def by (metis (no_types, lifting) list.set_sel(2))

    moreover 
    from \<open>wf_env e'\<close> have "(\<forall> v. v \<notin> visited ?e2 \<longrightarrow> \<S> ?e2 v = {v})"
      by (auto simp: wf_env_def)

    moreover have "\<Union> {\<S> ?e2 v | v . v \<in> set (stack ?e2)} = visited ?e2 - explored ?e2"
    proof -
      have 1: "\<Union> {\<S> e' v | v . v \<in> set (stack e')} = visited e' - explored e'"
        using \<open>wf_env e'\<close> by (simp add: wf_env_def)
      also have "\<dots> = \<Union> {\<S> ?e2 v | v . v \<in> set (stack e')}" 
        using Se'e2_eq 1 by auto
      from notempty stack2 
      have stacke':"set (stack e') = set (stack ?e2) \<union> {v}"
        by simp
      hence 2:"\<Union> {\<S> ?e2 v | v . v \<in> set (stack e')} = (\<Union>{\<S> ?e2 v | v . v \<in> set (stack ?e2)}) \<union> (\<S> ?e2 v)"
        by auto
      have exploredD: "explored e' = explored ?e2 - (\<S> ?e2 v)"
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
      moreover 
      have disjoint:"(\<Union>{\<S> ?e2 v | v . v \<in> set (stack ?e2)}) \<inter> (\<S> ?e2 v) = {}"
      proof -
        from \<open>wf_env e'\<close> onStackOneRepr Se'e2_eq True notempty stack2 stacke'
        have "\<forall> w. w \<in> set (stack ?e2) \<longrightarrow> \<S> ?e2 w \<inter> \<S> ?e2 v = {}" 
          unfolding wf_env_def
          by (metis (no_types, lifting) Un_iff distinct.simps(2) insertCI)
        thus ?thesis
          by blast
      qed
      ultimately
      have "(\<Union>{\<S> ?e2 v | v . v \<in> set (stack ?e2)}) \<union> (\<S> ?e2 v) = (visited ?e2 - explored ?e2) \<union> (\<S> ?e2 v)"
        by auto
      moreover
      from 1 2 exploredD
      have "(visited ?e2 - explored ?e2) \<inter> (\<S> ?e2 v) = {}" 
        by force
      ultimately show ?thesis
        by (smt (verit, best) Int_Un_distrib Int_commute Un_Int_eq(3) disjoint)
    qed
    
    moreover
    from 1 stack2 have "\<forall> x y. x \<preceq> y in stack ?e2 \<longrightarrow> reachable y x"
      by (auto simp: pre_dfs_def wf_env_def)

    moreover 
    from \<open>wf_env e'\<close> have "\<forall> x. is_subscc (\<S> ?e2 x)"
      by (simp add: wf_env_def)

    moreover have "\<forall>x \<in> explored ?e2. \<forall>y. reachable x y \<longrightarrow> y \<in> explored ?e2"
    proof (clarify)
      fix x y
      assume asm: "x \<in> explored ?e2" "reachable x y"
      show "y \<in> explored ?e2"
      proof (cases "x \<in> explored e'")
        case True
        with \<open>wf_env e'\<close> \<open>reachable x y\<close> show ?thesis
          by (simp add: wf_env_def)
      next
        case False
        with asm have "x \<in> \<S> e' v"
          by simp
        with \<open>explored ?e2 \<subseteq> visited ?e2\<close> have "x \<in> visited e'"
          by auto
        from \<open>x \<in> \<S> e' v\<close> \<open>wf_env e'\<close> have "reachable v x"
          by (auto simp: wf_env_def is_subscc_def)
        have "y \<in> visited e'"
        proof (rule ccontr)
          assume "y \<notin> visited e'"
          with reachable_visited[OF \<open>wf_env e'\<close> \<open>x \<in> visited e'\<close> \<open>reachable x y\<close>]
          obtain n m where
            "n \<in> visited e'" "m \<in> successors n - vsuccs e' n"
            "reachable x n" "reachable m y"
            by blast
          from \<open>wf_env e'\<close> \<open>m \<in> successors n - vsuccs e' n\<close>
          have "n \<notin> explored e'"
            by (auto simp: wf_env_def)
          with \<open>n \<in> visited e'\<close> \<open>wf_env e'\<close> obtain n' where
            "n' \<in> set (stack e')" "n \<in> \<S> e' n'"
            unfolding wf_env_def
            by (smt (verit, ccfv_threshold) Diff_iff Union_iff mem_Collect_eq)
          have "n' = v"
          proof (rule ccontr)
            assume "n' \<noteq> v"
            with \<open>n' \<in> set (stack e')\<close> \<open>v = hd (stack e')\<close>
            have "n' \<in> set (tl (stack e'))"
              by (metis emptyE hd_Cons_tl set_ConsD set_empty)
            moreover
            from \<open>n \<in> \<S> e' n'\<close> \<open>wf_env e'\<close> have "reachable n n'"
              by (auto simp: wf_env_def is_subscc_def)
            with \<open>reachable v x\<close> \<open>reachable x n\<close> reachable_trans have "reachable v n'"
              by blast
            ultimately show "False"
              using 3 \<open>v = hd (stack e')\<close> by (auto simp: post_dfss_def)
          qed
          with \<open>n \<in> \<S> e' n'\<close> \<open>m \<in> successors n - vsuccs e' n\<close> explored_vsuccs
          show "False"
            by auto
        qed
        show ?thesis
        proof (cases "y \<in> explored e'")
          case True
          then show ?thesis
            by simp
        next
          case False
          from False \<open>y \<in> visited e'\<close> \<open>wf_env e'\<close> have "y \<in> \<Union> {\<S> e' v | v. v \<in> set (stack e')}"
            by (simp add: wf_env_def)
          then obtain n where ndef: "n \<in> set (stack e')" "(y \<in> \<S> e' n)"
            by force
          show ?thesis
          proof (cases "n = v")
            case True
            with ndef show ?thesis by simp
          next
            case False
            with ndef notempty have "n \<in> set (tl (stack e'))"
              by simp
            moreover
            from \<open>wf_env e'\<close> have "is_subscc (\<S> e' n)" "n \<in> \<S> e' n"
              unfolding wf_env_def by auto
            with ndef have "reachable y n"
              by (auto simp: is_subscc_def)
            hence "reachable v n"
              using \<open>reachable v x\<close> \<open>reachable x y\<close> reachable_trans by blast
            ultimately show ?thesis
              using \<open>v = hd (stack e')\<close> 3 by (simp add: post_dfss_def)
          qed
        qed
      qed
    qed

    moreover
    {
      fix x y u
      assume xy: "x \<preceq> y in stack ?e2" "x \<noteq> y"
         and u: "u \<in> \<S> ?e2 x" "reachable_avoiding u y (unvisited ?e2 x)"
      from xy notempty stack2
      have "x \<preceq> y in stack e'"
        by (metis head_precedes insert_iff list.simps(15) precedes_in_tail precedes_mem(2))
      with \<open>wf_env e'\<close> \<open>x \<noteq> y\<close> u have "False"
        by (auto simp: wf_env_def unvisited_def)
    }

    moreover have "\<forall> S \<in> sccs ?e2. is_scc S"
    proof (clarify)
      fix S
      assume asm:"S \<in> sccs ?e2"
      show "is_scc S"
      proof (cases "S = \<S> e' v")
        case True
        with \<open>wf_env e'\<close> have "S \<noteq> {}"
          unfolding wf_env_def by (metis empty_iff)
        from \<open>wf_env e'\<close> True have subscc:"is_subscc S"
          by (simp add: wf_env_def)
        {
          assume contrad: "\<not> is_scc S"
          with \<open>S \<noteq> {}\<close> \<open>is_subscc S\<close> obtain S' where
            S'_def: "S' \<noteq> S" "S \<subseteq> S'" "is_subscc S'" 
            unfolding is_scc_def by blast
          then obtain x where "x \<in> S' \<and> x \<notin> S"
            by blast
          with True S'_def \<open>wf_env e'\<close>
          have xv: "reachable v x \<and> reachable x v"
            unfolding wf_env_def is_subscc_def by (metis in_mono)
          from \<open>\<forall>v w. w \<in> \<S> ?e2 v \<longleftrightarrow> (\<S> ?e2 v = \<S> ?e2 w)\<close>
          have "v \<in> explored ?e2"
            by auto
          with \<open>\<forall> x \<in> explored ?e2. \<forall> y. reachable x y \<longrightarrow> y \<in> explored ?e2\<close>
               xv \<open>S = \<S> e' v\<close> \<open>x \<in> S' \<and> x \<notin> S\<close>
          have "x \<in> explored e'"
            by auto
          with \<open>wf_env e'\<close> xv have "v \<in> explored e'"
            by (auto simp: wf_env_def)
          with \<open>wf_env e'\<close> notempty have "\<S> e' v =  \<S> e' x"
            by (auto simp: wf_env_def)
          with \<open>wf_env e'\<close> have "x \<in> \<S> e' v"
            by (auto simp: wf_env_def)
          with \<open>S = \<S> e' v\<close> \<open>x \<in> S' \<and> x \<notin> S\<close> have "False"
            by simp
        }
        then show ?thesis
          by blast
      next
        case False
        with asm \<open>wf_env e'\<close> show ?thesis
          by (auto simp: wf_env_def)
      qed
    qed

    moreover
    from \<open>wf_env e'\<close> have "\<Union> (sccs ?e2) = explored ?e2"
      by (auto simp: wf_env_def)

    moreover
    from 1 \<open>cstack e' = v # cstack e\<close> have "distinct (cstack ?e2)"
      by (auto simp: pre_dfs_def wf_env_def)

    moreover
    from 3 have "set (cstack ?e2) \<subseteq> visited ?e2"
      by (auto simp: post_dfss_def wf_env_def e1_def)

    moreover
    have "\<forall>n \<in> visited ?e2 - set (cstack ?e2). vsuccs ?e2 n = successors n"
    proof (clarsimp)
      fix n
      assume "n \<in> visited e'" "n \<notin> set (tl (cstack e'))"
      show "vsuccs e' n = successors n"
      proof (cases "n = v")
        case True
        with 3 show ?thesis 
          by (auto simp: post_dfss_def)
      next
        case False
        with \<open>n \<notin> set (tl (cstack e'))\<close> \<open>cstack e' = v # cstack e\<close>
        have "n \<notin> set (cstack e')"
          by simp
        with \<open>n \<in> visited e'\<close> \<open>wf_env e'\<close> show ?thesis
          by (auto simp: wf_env_def)
      qed
    qed

    moreover
    from 1 stack2 \<open>cstack e' = v # cstack e\<close>
    have "\<forall>n m. n \<preceq> m in stack ?e2 \<longrightarrow> n \<preceq> m in cstack ?e2"
      by (auto simp: pre_dfs_def wf_env_def)

    moreover
    have "\<forall>n \<in> set (stack ?e2). \<forall>m \<in> \<S> ?e2 n. m \<in> set (cstack ?e2) \<longrightarrow> m \<preceq> n in cstack ?e2"
    proof (clarsimp simp: \<open>cstack e' = v # cstack e\<close>)
      fix n m
      assume "n \<in> set (tl (stack e'))"
             "m \<in> \<S> e' n" "m \<in> set (cstack e)"
      with 3 have "m \<in> \<S> e n"
        by (auto simp: post_dfss_def e1_def)
      with 1 notempty \<open>n \<in> set (tl (stack e'))\<close> \<open>m \<in> set (cstack e)\<close>
      show "m \<preceq> n in cstack e"
        by (auto simp: pre_dfs_def wf_env_def)
    qed

    ultimately show ?thesis unfolding wf_env_def
      by meson
  qed

  moreover 
  from \<open>wf_env ?e2\<close> have "v \<in> explored ?e2"
    by (auto simp: wf_env_def)

  moreover
  from 3 have "vsuccs ?e2 v = successors v"
    by (simp add: post_dfss_def)

  moreover
  from 1 3 have "\<forall>w \<in> visited e. vsuccs ?e2 w = vsuccs e w"
    by (auto simp: pre_dfs_def post_dfss_def e1_def)

  moreover 
  from stack2 1 
  have "\<forall>n \<in> set (stack ?e2). reachable n v"
    by (simp add: pre_dfs_def)

  moreover 
  from stack2 have "\<exists> ns. stack e = ns @ (stack ?e2)"
    by auto

  moreover
  from 3 have "\<forall>n \<in> set (stack ?e2). \<S> ?e2 n = \<S> e n"
    by (auto simp: post_dfss_def e1_def)

  moreover
  from \<open>cstack e' = v # cstack e\<close> have "cstack ?e2 = cstack e"
    by simp

  ultimately show ?thesis
    unfolding post_dfs_def using e2 by simp
next
  case False
  with 2 have e':"dfs v e = e''"
    using False e''_def unfolding e1_def e'_def
    by (simp add: dfs.psimps)

  moreover have "wf_env e''"
  proof -
    have "visited e' = visited e''" "stack e' = stack e''" "explored e' = explored e''" "\<S> e' = \<S> e''" "vsuccs e' = vsuccs e''" "sccs e' = sccs e''"
      by (simp add: e''_def)+

    moreover from 3 have "wf_env e'"
      by (simp add: post_dfss_def)

    moreover 
    from \<open>wf_env e'\<close>
    have "distinct (stack e'')"
         "\<forall>v \<in> visited e''. reachable (root e'') v"
         "set (stack e'') \<subseteq> visited e''"
         "explored e'' \<subseteq> visited e''"
         "explored e'' \<inter> set (stack e'') = {}"
         "\<forall>v. vsuccs e'' v \<subseteq> successors v"
         "\<forall>v. vsuccs e'' v \<subseteq> visited e'"
         "\<forall>v. v \<notin> visited e'' \<longrightarrow> vsuccs e'' v = {}"
         "\<forall>v. v \<in> explored e'' \<longrightarrow> vsuccs e'' v = successors v"
         "\<forall>v w. w \<in> \<S> e'' v \<longleftrightarrow> (\<S> e'' v = \<S> e'' w)"
         "\<forall>v \<in> set (stack e''). \<forall> w \<in> set (stack e''). v \<noteq> w \<longrightarrow> \<S> e'' v \<inter> \<S> e'' w = {}"
         "\<forall>v. v \<notin> visited e'' \<longrightarrow> \<S> e'' v = {v}"
         "\<forall> x. is_subscc (\<S> e'' x)"
         "\<Union> {\<S> e'' v | v. v \<in> set (stack e'')} = visited e'' - explored e''"
         "\<forall> x y. x \<preceq> y in stack e'' \<longrightarrow> reachable y x"
         "\<forall> x \<in> explored e''. \<forall> y. reachable x y \<longrightarrow> y \<in> explored e''"
         "\<forall> S \<in> sccs e''. is_scc S"
         "\<Union> (sccs e'') = explored e''"
      by (auto simp: e''_def wf_env_def)

    moreover
    from \<open>wf_env e'\<close>
    have "(\<forall>x y. x \<preceq> y in stack e'' \<and> x \<noteq> y \<longrightarrow>
              (\<forall>u \<in> \<S> e'' x. \<not> reachable_avoiding u y (unvisited e'' x)))"
      by (force simp: e''_def wf_env_def unvisited_def)

    moreover
    from \<open>wf_env e'\<close> have "distinct (cstack e'')"
      by (auto simp: e''_def wf_env_def distinct_tl)

    moreover
    from 3 have "set (cstack e'') \<subseteq> visited e''"
      apply (simp add: e''_def)
      unfolding post_dfss_def wf_env_def
      by (metis Diff_cancel Diff_iff empty_set hd_Cons_tl insert_subset list.set_sel(1) list.simps(15) precedes_refl)

    moreover have "\<forall>n \<in> visited e'' - set (cstack e''). vsuccs e'' n = successors n"
    proof -
      have 1:"\<forall>n \<in> visited e' - set (cstack e'). vsuccs e' n = successors n" using 3 unfolding post_dfss_def wf_env_def
        by meson

      show ?thesis
      proof (clarify)
        fix n
        assume asm:"n \<in> visited e''" "n \<notin> set (cstack e'')"
        show "vsuccs e'' n = successors n"
        proof (cases "n \<notin> set(cstack e')")
          case True
          with 1 asm(1) show ?thesis
            by (auto simp: e''_def)
        next
          case False
          with asm(2) have "n = hd(cstack e')"
            apply (simp add: e''_def)
            by (metis Nil_tl list.collapse set_ConsD)
          moreover 
          from 3 have "vsuccs e' (hd (cstack e')) = successors (hd(cstack e'))"
            by (simp add: e'_def e1_def post_dfss_def)
          ultimately show ?thesis
            by (simp add: e''_def)
        qed
      qed
    qed

    moreover have "\<forall>n m. n \<preceq> m in stack e'' \<longrightarrow> n \<preceq> m in cstack e''"
    proof (clarsimp simp add: e''_def)
      fix n m
      assume nm: "n \<preceq> m in stack e'"
      with 3 have "n \<preceq> m in cstack e'"
        unfolding post_dfss_def wf_env_def
        by blast
      moreover
      have "n \<noteq> v"
      proof
        assume "n = v"
        with nm have "n \<in> set (stack e')"
          by (simp add: precedes_mem)
        with 3 \<open>n = v\<close> have "v = hd (stack e')"
          unfolding post_dfss_def wf_env_def
          by (metis (no_types, opaque_lifting) IntI equals0D list.set_sel(1))
        with \<open>v \<noteq> hd (stack e')\<close> show "False"
          by simp
      qed
      moreover
      from 3 have "cstack e' = v # cstack e"
        by (auto simp: post_dfss_def e1_def)
      ultimately show "n \<preceq> m in tl (cstack e')"
        by (simp add: precedes_in_tail)
    qed

    moreover 
    have "\<forall>n \<in> set (stack e''). \<forall>m \<in> \<S> e'' n. m \<in> set (cstack e'') \<longrightarrow> m \<preceq> n in cstack e''"
    proof (clarify)
      fix m n
      assume asm:"n \<in> set(stack e'')" "m \<in> \<S> e'' n" "m \<in> set (cstack e'')"
      from asm have "n \<in> set(stack e')" 
        using \<open>stack e' = stack e''\<close> by metis
      from asm have "m \<in> \<S> e' n" 
        using \<open>\<S> e' = \<S> e''\<close> by metis
      from asm have "m \<in> set(tl(cstack e'))" 
        by (simp add: e''_def)
      hence "m \<in> set(cstack e')"
        by (metis list.sel(2) list.set_sel(2))
      from wf_env_def[of e'] have "m \<preceq> n in cstack e'"
        using \<open>m \<in> \<S> e' n\<close> \<open>m \<in> set (cstack e')\<close> \<open>n \<in> set (stack e')\<close> \<open>wf_env e'\<close> by blast
      moreover have "cstack e'' = tl(cstack e')" by (simp add: e''_def)
      ultimately show "m \<preceq> n in cstack e''"
      proof -
        from \<open>m \<preceq> n in cstack e'\<close> have "m \<noteq> hd(cstack e') \<longrightarrow> m \<preceq> n in  tl(cstack e')"
          by (metis hd_Cons_tl list.sel(2) precedes_in_tail)
        have "distinct (cstack e')"
          using \<open>wf_env e'\<close> unfolding wf_env_def
          by blast
        hence "m \<noteq> hd(cstack e')" using asm(3) \<open>cstack e'' = tl (cstack e')\<close> \<open>m \<in> set (cstack e')\<close>
          by (metis distinct.simps(2) empty_iff list.exhaust_sel set_empty)
        thus ?thesis
          using \<open>cstack e'' = tl (cstack e')\<close> \<open>m \<noteq> hd (cstack e') \<longrightarrow> m \<preceq> n in tl (cstack e')\<close> by auto
      qed
    qed

    ultimately show ?thesis using e''_def unfolding wf_env_def
      by simp
  qed

  moreover from 3 have "v \<in> visited e''" unfolding e''_def
    by (auto simp: post_dfss_def sub_env_def e1_def)

  moreover have subenv:"sub_env e e''"
  proof -
    have "sub_env e e1"
      unfolding sub_env_def by (auto simp: e1_def)
    with 3 have "sub_env e e'"
      unfolding post_dfss_def by (auto elim: sub_env_trans)
    thus ?thesis unfolding sub_env_def by (auto simp add: e''_def)
  qed

  moreover
  from 3 have "vsuccs e'' v = successors v"
    unfolding e''_def by (simp add: post_dfss_def)

  moreover
  from 1 3 have "\<forall>w \<in> visited e. vsuccs e'' w = vsuccs e w"
    unfolding e''_def by (auto simp: pre_dfs_def post_dfss_def e1_def)

  moreover 
  from 3 have "\<forall> n \<in> set (stack e''). reachable n v"
    by (auto simp: e''_def post_dfss_def)

  moreover have "\<exists> ns. stack e = ns @ (stack e'')"
  proof -
    have "stack e' = stack e''" by (simp add: e''_def)
    from 3 obtain ns where ns: "stack e1 = ns @ stack e'"
      unfolding post_dfss_def by blast
    moreover have "stack e1 = v # stack e" by (simp add: e1_def)
    then have "v # stack e =  ns @ stack e'" using e1_def
      by (metis ns)
    then have "stack e = (tl ns) @ stack e'"
      using False unfolding e1_def
      by (metis append_Nil list.sel(1) list.sel(3) tl_append2)
    thus ?thesis
      by (simp add: \<open>stack e' = stack e''\<close>)
  qed

  moreover
  have "stack e'' \<noteq> []" "v \<in> \<S> e'' (hd (stack e''))"
       "\<forall>n \<in> set (tl (stack e'')). \<S> e'' n = \<S> e n"
    using 3 unfolding e''_def by (auto simp: post_dfss_def e1_def)

  moreover 
  from 3 have "cstack e'' = cstack e"
    by (auto simp: post_dfss_def e''_def e1_def)

  ultimately show ?thesis unfolding post_dfs_def
    by blast
qed

text \<open>
  The following lemma is the crucial ingredient to proving
  partial correctness: assuming termination (represented by
  the predicate @{text dfs_dfss_dom}) and the pre-condition
  of the functions, both @{text dfs} and @{text dfss}
  establish their post-conditions.
\<close>
lemma pre_post:
  shows
  "\<lbrakk>dfs_dfss_dom (Inl(v,e)); pre_dfs v e\<rbrakk> \<Longrightarrow> post_dfs v e (dfs v e)"
  "\<lbrakk>dfs_dfss_dom (Inr(v,e)); pre_dfss v e\<rbrakk> \<Longrightarrow> post_dfss v e (dfss v e)"
proof (induct rule: dfs_dfss.pinduct)
  fix v e
  assume dom: "dfs_dfss_dom (Inl(v,e))"
     and predfs: "pre_dfs v e"
     and prepostdfss: "\<And>e1. \<lbrakk> e1 = e \<lparr>visited := visited e \<union> {v}, stack := v # stack e, cstack := v # cstack e\<rparr>; pre_dfss v e1 \<rbrakk>
                            \<Longrightarrow> post_dfss v e1 (dfss v e1)"
  then show "post_dfs v e (dfs v e)"
    using pre_dfs_implies_post_dfs pre_dfs_pre_dfss by auto
next
  fix v e
  assume dom: "dfs_dfss_dom (Inr(v,e))"
     and predfss: "pre_dfss v e"
     and prepostdfs: 
           "\<And>vs w. 
             \<lbrakk> vs = successors v - vsuccs e v; vs \<noteq> {}; w = (SOME x. x \<in> vs); 
               w \<notin> explored e; w \<notin> visited e; pre_dfs w e \<rbrakk>
             \<Longrightarrow> post_dfs w e (dfs w e)"
     and prepostdfss:
           "\<And>vs w e' e''. 
             \<lbrakk> vs = successors v - vsuccs e v; vs \<noteq> {}; w = (SOME x. x \<in> vs); 
               e' = (if w \<in> explored e then e 
                     else if w \<notin> visited e then dfs w e 
                     else unite v w e); 
               e'' = e'\<lparr>vsuccs := \<lambda>x. if x = v then vsuccs e' v \<union> {w} 
                                      else vsuccs e' x\<rparr> ;
               pre_dfss v e'' \<rbrakk>
             \<Longrightarrow> post_dfss v e'' (dfss v e'')"
  show "post_dfss v e (dfss v e)"
  proof -
    let ?vs = "successors v - vsuccs e v"
    from predfss have "v \<in> visited e"
      by (simp add: pre_dfss_def)
    from predfss have "v \<notin> explored e"
      unfolding pre_dfss_def wf_env_def is_subscc_def
      by (metis disjoint_iff list.set_sel(1))

    show ?thesis
    proof (cases "?vs = {}") 
      case True
      with dom have return_e: "dfss v e = e" 
        by (simp add: dfss.psimps)
      moreover have "wf_env e"
        using predfss by (simp add: pre_dfss_def)
      moreover have "vsuccs e v = successors v"
        using True \<open>wf_env e\<close> unfolding wf_env_def
        by (meson Diff_eq_empty_iff subset_antisym)
      moreover have "sub_env e e"
        by (simp add: sub_env_def)
      moreover have "\<forall>w \<in> successors v. w \<in> explored e \<union> \<S> e (hd (stack e))"
        using predfss \<open>vsuccs e v = successors v\<close> by (simp add: pre_dfss_def)
      moreover have "\<forall> n \<in> set (stack e). reachable n v"
        using pre_dfss_def predfss by blast
      moreover have "stack e \<noteq> []"
        using pre_dfss_def predfss by blast
      moreover have "\<exists> ns. stack e = ns @ (stack e)"
        by simp
      moreover have "v \<in> \<S> e (hd (stack e))"
        using pre_dfss_def predfss by blast
      moreover
      {
        fix n
        assume asm: "hd (stack e) = v"
                    "n \<in> set (tl (stack e))"
                    "reachable v n"
        with \<open>stack e \<noteq> []\<close> have "v \<preceq> n in stack e"
          by (metis head_precedes hd_Cons_tl list.set_sel(2))
        moreover
        from \<open>wf_env e\<close> \<open>stack e \<noteq> []\<close> asm have "v \<noteq> n"
          unfolding wf_env_def
          by (metis distinct.simps(2) list.exhaust_sel)
        moreover
        from \<open>wf_env e\<close> have "v \<in> \<S> e v"
          by (auto simp: wf_env_def)
        moreover
        {
          fix a b
          assume "a \<in> \<S> e v" "b \<in> successors a - vsuccs e a"
          with \<open>vsuccs e v = successors v\<close> have "a \<noteq> v"
            by auto
          from \<open>pre_dfss v e\<close> have "stack e \<noteq> []"
            by (simp add: pre_dfss_def)
          with \<open>hd (stack e) = v\<close> have "v \<in> set (stack e)"
            by auto
          with \<open>a \<noteq> v\<close> \<open>a \<in> \<S> e v\<close> \<open>wf_env e\<close> have "a \<in> visited e"
            unfolding wf_env_def by (metis singletonD)
          have "False"
          proof (cases "a \<in> set (cstack e)")
            case True
            with \<open>v \<in> set (stack e)\<close> \<open>a \<in> \<S> e v\<close> \<open>wf_env e\<close>
            have "a \<preceq> v in cstack e"
              by (auto simp: wf_env_def)
            moreover
            from \<open>pre_dfss v e\<close> obtain ns where "cstack e = v # ns"
              by (auto simp: pre_dfss_def)
            moreover
            from \<open>pre_dfss v e\<close> have "distinct (cstack e)"
              by (simp add: pre_dfss_def wf_env_def)
            ultimately have "a = v"
              using tail_not_precedes by force 
            with \<open>a \<noteq> v\<close> show ?thesis
              by simp
          next
            case False
            with \<open>a \<in> visited e\<close> \<open>wf_env e\<close> have "vsuccs e a = successors a"
              by (auto simp: wf_env_def)
            with \<open>b \<in> successors a - vsuccs e a\<close> show ?thesis
              by simp
          qed
        }
        hence "unvisited e v = {}"
          by (auto simp: unvisited_def)

        ultimately have "\<not> reachable_avoiding v n {}"
          using \<open>wf_env e\<close> unfolding wf_env_def by metis
        with \<open>reachable v n\<close> have "False"
          by (simp add: ra_empty)
      }
      ultimately show ?thesis
        by (force simp: post_dfss_def)
    next
      case vs_case: False
      define w where "w = (SOME x. x \<in> ?vs)"
      define e' where "e' = (if w \<in> explored e then e 
                             else if w \<notin> visited e then dfs w e 
                             else unite v w e)"
      define e'' where "e'' = (e'\<lparr>vsuccs := \<lambda>x. if x=v then vsuccs e' v \<union> {w} else vsuccs e' x\<rparr>)"

      from dom vs_case have dfss: "dfss v e = dfss v e''"
        apply (auto simp: dfss.psimps w_def e'_def e''_def)
        using w_def e'_def by auto

      from vs_case have wvs: "w \<in> ?vs"
        unfolding w_def by (metis some_in_eq)
      show ?thesis
      proof (cases "w \<in> explored e")
        case True
        hence e': "e' = e"
          by (simp add: e'_def)
        with predfss wvs True
        have "pre_dfss v e''"
          by (auto simp: e''_def pre_dfss_pre_dfss_explored)
        with prepostdfss vs_case 
        have post'': "post_dfss v e'' (dfss v e'')"
          by (auto simp: w_def e'_def e''_def)

        moreover
        from post''
        have "\<forall>u \<in> visited e - {v}. vsuccs (dfss v e'') u = vsuccs e u"
          by (auto simp: post_dfss_def e' e''_def)

        moreover
        have "sub_env e e''"
          by (auto simp: sub_env_def e' e''_def)
        with post'' have "sub_env e (dfss v e'')"
          by (auto simp: post_dfss_def elim: sub_env_trans)

        moreover
        from e' have "stack e'' = stack e" "\<S> e'' = \<S> e"
          by (auto simp add: e''_def)

        moreover
        have "cstack e'' = cstack e"
          by (simp add: e''_def e')

        ultimately show ?thesis
          by (auto simp: dfss post_dfss_def)
      next
        case notexplored: False
        then show ?thesis
        proof (cases "w \<notin> visited e")
          case True
          hence "e' = dfs w e" using e'_def notexplored
            by auto
          with True notexplored pre_dfss_pre_dfs predfss prepostdfs vs_case w_def
          have postdfsw: "post_dfs w e e'"
            by (metis DiffD1 some_in_eq)
          with predfss wvs True \<open>e' = dfs w e\<close>
          have "pre_dfss v e''"
            by (auto simp: e''_def pre_dfss_post_dfs_pre_dfss)
          with prepostdfss vs_case 
          have post'': "post_dfss v e'' (dfss v e'')"
            by (auto simp: w_def e'_def e''_def)

          moreover
          have "\<forall>u \<in> visited e - {v}. vsuccs (dfss v e'') u = vsuccs e u"
          proof
            fix u
            assume "u \<in> visited e - {v}"
            with postdfsw 
            have u: "vsuccs e' u = vsuccs e u" "u \<in> visited e'' - {v}"
              by (auto simp: post_dfs_def sub_env_def e''_def)
            with post'' have "vsuccs (dfss v e'') u = vsuccs e'' u"
              by (auto simp: post_dfss_def)
            with u show "vsuccs (dfss v e'') u = vsuccs e u"
              by (simp add: e''_def)
          qed

          moreover
          have "sub_env e (dfss v e'')"
          proof -
            from postdfsw have "sub_env e e'"
              by (simp add: post_dfs_def)
            moreover
            have "sub_env e' e''"
              by (auto simp: sub_env_def e''_def)
            moreover
            from post'' have "sub_env e'' (dfss v e'')"
              by (simp add: post_dfss_def)
            ultimately show ?thesis
              using sub_env_trans by metis
          qed

          moreover
          have "\<exists>ns. stack e = ns @ (stack (dfss v e''))"
          proof -
            from postdfsw obtain xs where "stack e = xs @ stack e''"
              by (auto simp: post_dfs_def e''_def)
            moreover
            from post'' obtain ys where "stack e'' = ys @ stack (dfss v e'')"
              by (auto simp: post_dfss_def)
            ultimately show ?thesis
              by auto
          qed

          moreover
          {
            fix n
            assume n: "n \<in> set (tl (stack (dfss v e'')))"
            with post'' have "\<S> (dfss v e'') n = \<S> e' n"
              by (simp add: post_dfss_def e''_def)
            moreover
            from \<open>pre_dfss v e''\<close> have "stack e' \<noteq> []"
              by (simp add: pre_dfss_def e''_def)
            from n post'' have "n \<in> set (tl (stack e''))"
              unfolding post_dfss_def
              by (metis Un_iff list.set_sel(2) self_append_conv2 set_append tl_append2)
            with postdfsw \<open>stack e' \<noteq> []\<close> have "\<S> e' n = \<S> e n"
              apply (simp add: post_dfs_def e''_def)
              by (metis list.set_sel(2))
            ultimately have "\<S> (dfss v e'') n = \<S> e n"
              by simp
          }

          moreover
          from postdfsw have "cstack e'' = cstack e"
            by (auto simp: post_dfs_def e''_def)

          ultimately show ?thesis
            by (auto simp: dfss post_dfss_def)

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

          from \<open>wf_env e\<close> \<open>w \<in> visited e\<close> \<open>w \<notin> explored e\<close>
          have "w \<in> \<Union> {\<S> e n | n. n \<in> set (stack e)}"
            by (simp add: wf_env_def)
          then obtain n where "n \<in> set (stack e)" "w \<in> \<S> e n"
            by auto
          hence sfx: "sfx \<noteq> [] \<and> w \<in> \<S> e (hd sfx)"
            unfolding sfx_def
            by (metis dropWhile_eq_Nil_conv hd_dropWhile)
          with \<open>wf_env e\<close> \<open>stack e = pfx @ sfx\<close>
          have pfx: "set pfx \<union> {hd sfx} \<subseteq> cc"
            unfolding wf_env_def cc_def 
            by (smt (verit) Union_iff mem_Collect_eq subset_eq)

          have "\<forall>n \<in> set (tl sfx). \<S> e n \<inter> cc = {}"
          proof -
            {
              fix n u
              assume "n \<in> set (tl sfx)" "u \<in> \<S> e n" "u \<in> cc"
              from sfx \<open>n \<in> set (tl sfx)\<close> \<open>stack e = pfx @ sfx\<close> \<open>wf_env e\<close>
              have n: "n \<in> set (stack e) - (set pfx \<union> {hd sfx})"
                unfolding wf_env_def
                by (metis Diff_iff Int_iff Un_iff distinct.simps(2) distinct_append empty_iff list.exhaust_sel list.set_sel(2) set_append singletonD)
              from \<open>u \<in> cc\<close> obtain n' where
                n': "n' \<in> set pfx \<union> {hd sfx}" "u \<in> \<S> e n'"
                by (auto simp: cc_def)
              with n \<open>stack e = pfx @ sfx\<close> sfx \<open>wf_env e\<close>
              have "\<S> e n \<inter> \<S> e n' = {}"
                unfolding wf_env_def
                by (metis (no_types, lifting) DiffE UnCI UnE list.set_sel(1) set_append singleton_iff)
              with \<open>u \<in> \<S> e n\<close> \<open>u \<in> \<S> e n'\<close> have "False"
                by auto
            }
            thus ?thesis by auto
          qed
          with \<open>wf_env e\<close> sfx \<open>stack e = pfx @ sfx\<close>
          have tl_sfx_not_in_cc: "\<forall>x \<in> set (tl sfx). x \<notin> cc"
            unfolding wf_env_def cc_def
            by (metis (no_types, lifting) disjoint_insert(1) insert_Diff)

          from \<open>e' = unite v w e\<close>
          have e'_def: "e' = e\<lparr>\<S> := \<lambda>x. if x \<in> cc then cc else \<S> e x, stack := sfx\<rparr>" 
            using unite_def cc_def pfx_def sfx_def by auto

          from pfx have hd_sfx: "\<S> e' (hd sfx) = cc"
            by (simp add: e'_def)

          from sfx have "stack e' = (hd sfx) # tl sfx"
            by (auto simp: e'_def)
          moreover
          from tl_sfx_not_in_cc have "\<forall>v \<in> set (tl sfx). \<S> e' v = \<S> e v"
            by (simp add: e'_def)
          ultimately
          have "(\<Union> {\<S> e' v | v. v \<in> set (stack e')}) 
                = cc \<union> (\<Union> {\<S> e v | v. v \<in> set (tl sfx)})"
            using hd_sfx by auto
          moreover
          from \<open>stack e = pfx @ sfx\<close> sfx
          have "stack e = pfx @ (hd sfx # tl sfx)"
            by auto
          ultimately
          have s_equal: "(\<Union> {\<S> e' v | v. v \<in> set (stack e')}) 
                         = (\<Union> {\<S> e v | v. v \<in> set (stack e)})"
            by (auto simp: cc_def)

          have "sub_env e e'"
          proof -
            have "\<forall> x. \<S> e x \<subseteq> \<S> e' x"
            proof
              fix x
              show "\<S> e x \<subseteq> \<S> e' x"
              proof (cases "x \<in> cc")
                case True
                then obtain n where
                  n: "n \<in> set pfx \<union> {hd sfx}" "x \<in> \<S> e n"
                  by (auto simp: cc_def)
                with \<open>wf_env e\<close> have "\<S> e x = \<S> e n"
                  by (auto simp: wf_env_def)
                with \<open>n \<in> set pfx \<union> {hd sfx}\<close> have "\<S> e x \<subseteq> cc"
                  by (auto simp: cc_def)
                moreover
                from n have "x \<in> cc"
                  by (auto simp: cc_def)
                ultimately show ?thesis
                  by (simp add: e'_def)
              next
                case False
                then show ?thesis
                  by (simp add: e'_def)
              qed
            qed
            with s_equal show ?thesis
              by (simp add: sub_env_def e'_def)
          qed

          from predfss wvs notexplored False \<open>e' = unite v w e\<close>
          have "pre_dfss v e''"
            by (auto simp: e''_def pre_dfss_unite_pre_dfss)

          with prepostdfss vs_case \<open>e' = unite v w e\<close>  \<open>w \<notin> explored e\<close> \<open>w \<in> visited e\<close>
          have post'': "post_dfss v e'' (dfss v e'')"
            by (auto simp: w_def e''_def)

          moreover
          have "\<forall>u \<in> visited e - {v}. vsuccs (dfss v e'') u = vsuccs e u"
          proof
            fix u
            assume "u \<in> visited e - {v}"
            hence u: "vsuccs e' u = vsuccs e u" "u \<in> visited e'' - {v}"
              by (auto simp: e''_def e'_def)
            with post'' have "vsuccs (dfss v e'') u = vsuccs e'' u"
              by (auto simp: post_dfss_def)
            with u show "vsuccs (dfss v e'') u = vsuccs e u"
              by (simp add: e''_def)
          qed

          moreover
          have "sub_env e (dfss v e'')"
          proof -
            have "sub_env e' e''"
              by (auto simp: sub_env_def e''_def)
            moreover
            from post'' have "sub_env e'' (dfss v e'')"
              by (simp add: post_dfss_def)
            ultimately show ?thesis
              using \<open>sub_env e e'\<close> sub_env_trans by metis
          qed

          moreover
          from post'' \<open>stack e = pfx @ sfx\<close>
          have "\<exists>ns. stack e = ns @ (stack (dfss v e''))"
            apply (simp add: post_dfss_def e''_def e'_def)
            by (metis (no_types, lifting) append_assoc)

          moreover
          {
            fix n
            assume n: "n \<in> set (tl (stack (dfss v e'')))"
            with post'' have "\<S> (dfss v e'') n = \<S> e'' n"
              by (simp add: post_dfss_def)
            moreover
            from sfx have "stack e'' \<noteq> []"
              by (simp add: e''_def e'_def)
            with n post''
            have "n \<in> set (tl (stack e''))"
              unfolding post_dfss_def
              by (metis Un_iff list.set_sel(2) self_append_conv2 set_append tl_append2)
            with tl_sfx_not_in_cc
            have "\<S> e'' n = \<S> e n"
              by (auto simp: e''_def e'_def)
            ultimately have "\<S> (dfss v e'') n = \<S> e n"
              by simp
          }

          moreover
          from post'' have "cstack (dfss v e'') = cstack e"
            by (auto simp: post_dfss_def e''_def e'_def)

          ultimately show ?thesis
            by (auto simp: dfss post_dfss_def)
        qed
      qed
    qed
  qed
qed

text \<open>
  The algorithm is initially called with an environment that
  initializes the root node and trivializes all other components.
\<close>
definition init_env where
  "init_env v = \<lparr>
    root = v,
    \<S> = (\<lambda>u. {u}),
    explored = {},
    visited = {},
    vsuccs = (\<lambda>u. {}),
    sccs = {},
    stack = [],
    cstack = []
   \<rparr>"

text \<open>
  We can now show partial correctness of the algorithm:
  applied to some node @{text "v"} and the empty environment,
  it computes the set of strongly connected components in
  the subgraph reachable from node @{text "v"}. In particular,
  if @{text "v"} is a root of the graph, the algorithm computes
  the set of SCCs of the graph.
\<close>

theorem partial_correctness:
  fixes v
  defines "e \<equiv> dfs v (init_env v)"
  assumes "dfs_dfss_dom (Inl (v, init_env v))"
  shows "sccs e = {S . is_scc S \<and> (\<forall>n\<in>S. reachable v n)}"
    (is "_ = ?rhs")
proof -
  have "pre_dfs v (init_env v)"
    by (auto simp: pre_dfs_def wf_env_def init_env_def is_subscc_def
             dest: precedes_mem)
  with assms have post: "post_dfs v (init_env v) e"
    by (auto dest: pre_post)
  hence "cstack e = []"
    by (auto simp: post_dfs_def init_env_def)
  have "stack e = []"
  proof (rule ccontr)
    assume "stack e \<noteq> []"
    hence "hd (stack e) \<preceq> hd (stack e) in stack e"
      by simp
    with post have "hd (stack e) \<preceq> hd (stack e) in cstack e"
      unfolding post_dfs_def wf_env_def
      by blast
    with \<open>cstack e = []\<close> show "False"
      by (auto dest: precedes_mem)
  qed
  with post have vexp: "v \<in> explored e"
    by (simp add: post_dfs_def)
  from post \<open>stack e = []\<close> have "explored e = visited e"
    by (auto simp: post_dfs_def wf_env_def)
  have "sccs e \<subseteq> ?rhs"
  proof
    fix S
    assume S: "S \<in> sccs e"
    with post have "is_scc S"
      by (simp add: post_dfs_def wf_env_def)
    moreover
    from S post have "S \<subseteq> explored e"
      unfolding post_dfs_def wf_env_def
      by blast
    with post \<open>explored e = visited e\<close> have "\<forall>n\<in>S. reachable v n"
      by (auto simp: post_dfs_def wf_env_def sub_env_def init_env_def)
    ultimately show "S \<in> ?rhs"
      by auto
  qed
  moreover
  {
    fix S
    assume "is_scc S" "\<forall>n\<in>S. reachable v n"
    from \<open>\<forall>n\<in>S. reachable v n\<close> vexp post
    have "S \<subseteq> \<Union> (sccs e)"
      unfolding post_dfs_def wf_env_def by (metis subset_eq)
    with \<open>is_scc S\<close> obtain S' where S': "S' \<in> sccs e \<and> S \<inter> S' \<noteq> {}"
      unfolding is_scc_def
      by (metis Union_disjoint inf.absorb_iff2 inf_commute)
    with post have "is_scc S'"
      by (simp add: post_dfs_def wf_env_def)
    with S' \<open>is_scc S\<close> have "S \<in> sccs e"
      by (auto dest: scc_partition)
  }
  ultimately show ?thesis by blast
qed

section \<open>Proof of termination and total correctness\<close>

text
\<open>
Three clauses: 
- dfss from dfs : Inr(v, e1), Inl(v, e)
- dfs  from dfss: Inl(w, e), Inr(v, e)
- dfss from dfss: Inr(v, e''), Inr(v, e)
\<close>

definition dfs_dfss_term where
  "dfs_dfss_term \<equiv>
    { (Inr(v, e1::'v env), Inl(v::'v, e::'v env)) | v e e1. v \<in> vertices - visited e \<and> visited e1 = visited e \<union> {v} }
  \<union> { (Inl(w::'v, e), Inr(v::'v, e:: 'v env)) | v w e. v \<in> vertices}
  \<union> { (Inr(v::'v, e''::'v env), Inr(v::'v, e::'v env)) | v e e''. v \<in> vertices \<and> sub_env e e'' \<and> (\<exists>w \<in> vertices. w \<notin> vsuccs e v \<and> w \<in> vsuccs e'' v)}"

fun dfs_dfss_to_tuple where
  "dfs_dfss_to_tuple (Inl(v::'v, e::'v env)) = (vertices - visited e, vertices \<times> vertices - {(u,u') | u u'. u' \<in> vsuccs e u}, 0)"
| "dfs_dfss_to_tuple (Inr(v::'v, e::'v env)) = (vertices - visited e, vertices \<times> vertices - {(u,u') | u u'. u' \<in> vsuccs e u}, 1::nat)"


lemma wf_term: "wf dfs_dfss_term"
proof -
  let ?r = "(finite_psubset :: ('v set \<times> 'v set) set)
            <*lex*> (finite_psubset :: ((('v \<times> 'v) set) \<times> ('v \<times> 'v) set) set)
            <*lex*> pred_nat"
  have "wf (finite_psubset :: ('v set \<times> 'v set) set)"
    by (rule wf_finite_psubset)
  moreover
  have "wf (finite_psubset :: ((('v \<times> 'v) set) \<times> ('v \<times> 'v) set) set)"
    by (rule wf_finite_psubset)
  ultimately have "wf ?r"
    using wf_pred_nat by blast
  moreover
  have "dfs_dfss_term \<subseteq> inv_image ?r dfs_dfss_to_tuple"
  proof (clarify)
    fix a b
    assume "(a,b) \<in> dfs_dfss_term"
    hence "(\<exists>v w e e''. a = Inr(v,e'') \<and> b = Inr(v,e) \<and> v \<in> vertices \<and> sub_env e e'' \<and> w \<in> vertices \<and> w \<notin> vsuccs e v \<and> w \<in> vsuccs e'' v)
         \<or> (\<exists>v e e1. a = Inr(v,e1) \<and> b = Inl(v,e) \<and> v \<in> vertices - visited e \<and> visited e1 = visited e \<union> {v})
         \<or> (\<exists>v w e. a = Inl(w,e) \<and> b = Inr(v,e))"
         (is "?c1 \<or> ?c2 \<or> ?c3")
      by (auto simp: dfs_dfss_term_def)
    then show "(a,b) \<in> inv_image ?r dfs_dfss_to_tuple"
    proof
      assume "?c1"
      then obtain v w e e'' where
        ab: "a = Inr(v, e'')" "b = Inr(v,e)" and
        vw: "v \<in> vertices" "w \<in> vertices" "w \<in> vsuccs e'' v" "w \<notin> vsuccs e v" and
        sub: "sub_env e e''"
        by blast
      from sub have "vertices - visited e'' \<subseteq> vertices - visited e"
        by (auto simp: sub_env_def)
      moreover
      from sub vw
      have "(vertices \<times> vertices - {(u,u') | u u'. u' \<in> vsuccs e'' u})
          \<subset> (vertices \<times> vertices - {(u,u') | u u'. u' \<in> vsuccs e u})"
        by (auto simp: sub_env_def)
      ultimately show ?thesis
        using vfin ab by auto
    next
      assume "?c2 \<or> ?c3"
      with vfin show ?thesis
        by (auto simp: pred_nat_def)
    qed
  qed
  ultimately show ?thesis
    using wf_inv_image wf_subset by blast
qed

theorem dfs_dfss_termination:
  "\<lbrakk>v \<in> vertices ; pre_dfs v e\<rbrakk> \<Longrightarrow> dfs_dfss_dom(Inl(v, e))"
  "\<lbrakk>v \<in> vertices ; pre_dfss v e\<rbrakk> \<Longrightarrow> dfs_dfss_dom(Inr(v, e))"
proof -
  { fix args
    have "(case args
          of Inl(v,e) \<Rightarrow> 
            v \<in> vertices \<and> pre_dfs v e
          |  Inr(v,e) \<Rightarrow> 
             v \<in> vertices \<and> pre_dfss v e)
        \<longrightarrow> dfs_dfss_dom args" (is "?P args \<longrightarrow> ?Q args")
    proof (rule wf_induct[OF wf_term])
      fix arg :: "('v \<times> 'v env) + ('v \<times> 'v env)"
      assume ih: "\<forall> arg'. (arg', arg) \<in> dfs_dfss_term \<longrightarrow> (?P arg' \<longrightarrow> ?Q arg')"
      show "?P arg \<longrightarrow> ?Q arg"
      proof
        assume P: "?P arg"
        show "?Q arg"
        proof (cases arg)
          case (Inl a)
          then obtain v e where a: "arg = Inl(v, e)" using dfs.cases by metis
          with P have pre: "v \<in> vertices \<and> pre_dfs v e"
            by simp
          let ?e1 = "e\<lparr>visited := visited e \<union> {v}, stack := v # stack e, cstack := v # cstack e\<rparr>"
          let ?recarg = "Inr(v, ?e1)"

          have "(?recarg, arg) \<in> dfs_dfss_term"
          proof -
            have "v \<in> vertices - visited e"
              using pre unfolding pre_dfs_def by simp
            moreover
            have "visited ?e1 = visited e \<union> {v}"
              by simp
            ultimately show ?thesis
              using a pre unfolding dfs_dfss_term_def
              by blast
          qed

          moreover
          have "?P ?recarg"
          proof -
            have "pre_dfss v ?e1"
              using pre pre_dfs_pre_dfss by auto
            thus ?thesis
              using pre by simp
          qed

          ultimately have "?Q ?recarg"
            using ih a by auto

          then have "?Q (Inl(v, e))"
            by (auto intro: dfs_dfss.domintros)

          then show ?thesis
            by (simp add: a)
        next
          case (Inr b)
          then obtain v e where b: "arg = Inr(v, e)" using dfs.cases by metis
          with P have pre: "v \<in> vertices \<and> pre_dfss v e"
            by simp
          let ?sw = "SOME w. w \<in> successors v \<and> w \<notin> vsuccs e v"
          have "?Q (Inr(v, e))"
          proof (rule dfs_dfss.domintros)
            fix w
            assume "w \<in> successors v"
                   "?sw \<notin> explored e"
                   "?sw \<notin> visited e"
                   "\<not> dfs_dfss_dom (Inl (?sw, e))"
            show "w \<in> vsuccs e v"
            proof (rule ccontr)
              assume "w \<notin> vsuccs e v"
              with \<open>w \<in> successors v\<close> have sw: "?sw \<in> successors v - vsuccs e v"
                by (metis (mono_tags, lifting) Diff_iff some_eq_imp)
              with pre \<open>?sw \<notin> visited e\<close> have "pre_dfs ?sw e"
                by (blast intro: pre_dfss_pre_dfs)
              moreover
              from pre sw sclosed have "?sw \<in> vertices"
                by blast
              moreover
              from pre have "(Inl(?sw,e), Inr(v,e)) \<in> dfs_dfss_term"
                by (simp add: dfs_dfss_term_def)
              ultimately have "dfs_dfss_dom (Inl(?sw,e))"
                using ih b by auto
              with \<open>\<not> dfs_dfss_dom (Inl (?sw, e))\<close> 
              show "False" ..
            qed
          next
            let ?e' = "dfs ?sw e"
            let ?e''= "?e'\<lparr>vsuccs := \<lambda>x. if x = v then vsuccs ?e' v \<union> {?sw} 
                                         else vsuccs ?e' x\<rparr>"
            fix w
            assume asm: "w \<in> successors v" "w \<notin> vsuccs e v"
                        "?sw \<notin> visited e" "?sw \<notin> explored e"
            from \<open>w \<in> successors v\<close> \<open>w \<notin> vsuccs e v\<close>
            have sw: "?sw \<in> successors v - vsuccs e v"
              by (metis (no_types, lifting) Diff_iff some_eq_imp)
            with pre \<open>?sw \<notin> visited e\<close> have "pre_dfs ?sw e"
              by (blast intro: pre_dfss_pre_dfs)
            moreover
            from pre sw sclosed have "?sw \<in> vertices"
              by blast
            moreover
            from pre have "(Inl(?sw, e), Inr(v,e)) \<in> dfs_dfss_term"
              by (simp add: dfs_dfss_term_def)
            ultimately have "dfs_dfss_dom (Inl(?sw, e))"
              using ih b by auto
            from this \<open>pre_dfs ?sw e\<close> have post: "post_dfs ?sw e ?e'"
              by (rule pre_post)
            hence "sub_env e ?e'"
              by (simp add: post_dfs_def)
            moreover
            have "sub_env ?e' ?e''"
              by (auto simp: sub_env_def)
            ultimately have "sub_env e ?e''"
              by (rule sub_env_trans)
            with pre \<open>?sw \<in> vertices\<close> sw
            have "(Inr(v, ?e''), Inr(v, e)) \<in> dfs_dfss_term"
              by (auto simp: dfs_dfss_term_def)
            moreover
            from pre post sw \<open>?sw \<notin> visited e\<close> have "pre_dfss v ?e''"
              by (blast intro: pre_dfss_post_dfs_pre_dfss)
            ultimately show "dfs_dfss_dom(Inr(v, ?e''))"
              using pre ih b by auto
          next
            fix w
            assume asm:"w \<in> successors v"
                   "w \<notin> vsuccs e v"
                   "?sw \<notin> visited e"
                   "?sw \<in> explored e"
            let ?e'' =  "e\<lparr>vsuccs := \<lambda>x. if x = v then vsuccs e v \<union> {?sw} else vsuccs e x\<rparr>"
            let ?recarg = "Inr(v, ?e'')"

            from asm have "?sw \<in> explored e - visited e" by simp
            then have "False" using pre asm(3) asm(4) unfolding pre_dfss_def wf_env_def
              by (meson subsetD)
            thus "?Q ?recarg"
              by simp 
          next
            fix w
            assume asm:"w \<in> successors v"
                   "w \<notin> vsuccs e v"
                   "?sw \<in> visited e"
                   "?sw \<in> explored e"
            let ?e'' =  "e\<lparr>vsuccs := \<lambda>x. if x = v then vsuccs e v \<union> {?sw} else vsuccs e x\<rparr>"
            let ?recarg = "Inr(v, ?e'')"

            have "(?recarg, arg) \<in> dfs_dfss_term"
            proof -
              have "sub_env e ?e''"
              proof -
                have "\<forall>u. vsuccs e u \<subseteq> vsuccs ?e'' u"
                proof
                  fix u
                  show "vsuccs e u \<subseteq> vsuccs ?e'' u"
                  proof (cases "u = v")
                    case True
                    then have "vsuccs ?e'' u = vsuccs e u \<union> {?sw}" by simp
                    then show ?thesis
                      by blast
                  next
                    case False
                    then have "vsuccs ?e'' u = vsuccs e u" by simp
                    then show ?thesis
                      by blast
                  qed
                qed
                then show ?thesis unfolding sub_env_def by simp
              qed

              moreover have "\<exists>u \<in> vertices. u \<notin> vsuccs e v \<and> u \<in> vsuccs ?e'' v"
              proof -
              have "?sw \<notin> vsuccs e v" using asm(1) asm(2)
                by (metis (no_types, lifting) tfl_some)
              moreover have "?sw \<in> vsuccs ?e'' v"
                by simp
              ultimately show ?thesis using pre asm(1) asm(2) sclosed
                by (metis (no_types, lifting) in_mono someI)
              qed
              ultimately show ?thesis
                using pre unfolding dfs_dfss_term_def
                using b by blast
            qed
            
            moreover have "?P ?recarg"
            proof -
              have "pre_dfss v ?e''"
              proof -
                from asm have "?sw \<in> successors v" using asm(1) asm(2)
                  by (metis (mono_tags, lifting) tfl_some)
                moreover have "?sw \<in> explored e" using asm by simp
                ultimately show ?thesis using pre asm pre_dfss_pre_dfss_explored by auto
              qed
              thus ?thesis using pre asm by simp
            qed

            ultimately show "?Q ?recarg"
              using ih b by auto
          next
            fix w
            assume asm:"w \<in> successors v"
                   "w \<notin> vsuccs e v"
                   "?sw \<in> visited e"
                   "?sw \<notin> explored e"
            let ?eu = "unite v ?sw e"
            let ?e'' = "?eu \<lparr> vsuccs := \<lambda>x. if x = v then vsuccs ?eu v \<union> {?sw} else vsuccs ?eu x\<rparr>"
            let ?recarg = "Inr(v, ?e'')"

            have "(?recarg, arg) \<in> dfs_dfss_term"
            proof -
              have "sub_env e ?e''"
              proof -
                from unite_mono asm have "sub_env e ?eu"
                  by (metis (no_types, lifting) pre tfl_some)
                
                moreover
                have "\<forall>u. vsuccs e u \<subseteq> vsuccs ?e'' u"
                proof -
                  have "\<forall> u. vsuccs ?eu u \<subseteq> vsuccs ?e'' u"
                  proof
                    fix u
                    show "vsuccs ?eu u \<subseteq> vsuccs ?e'' u"
                    proof (cases "u = v")
                      case True
                      then have "vsuccs ?e'' u = vsuccs ?eu u \<union> {?sw}" by simp
                      then show ?thesis
                        by blast
                    next
                      case False
                      then have "vsuccs ?e'' u = vsuccs ?eu u" by simp
                      then show ?thesis
                        by blast
                    qed
                  qed
                  thus ?thesis using \<open>sub_env e ?eu\<close> unfolding sub_env_def
                    by (meson subset_trans)
                qed
                ultimately show ?thesis
                  unfolding sub_env_def
                  by simp
              qed

              moreover
              have "\<exists>w \<in> vertices. w \<notin> vsuccs e v \<and> w \<in> vsuccs ?e'' v"
              proof -
              have "?sw \<notin> vsuccs e v" using asm(1) asm(2)
                by (metis (no_types, lifting) tfl_some)
              moreover have "?sw \<in> vsuccs ?e'' v"
                by simp
              ultimately show ?thesis using pre asm(1) asm(2) sclosed
                by (metis (no_types, lifting) in_mono someI)
              qed

              ultimately show ?thesis
                using pre asm b
                unfolding dfs_dfss_term_def
                by blast
            qed

            moreover have "?P ?recarg"
            proof -
              have "?sw \<in> successors v" "?sw \<notin> vsuccs e v" "?sw \<in> visited e" "?sw \<notin> explored e"
                using asm
                by (metis (mono_tags, lifting) tfl_some)+
              hence "pre_dfss v ?e''" using pre pre_dfss_unite_pre_dfss
                by simp
              thus ?thesis using pre
                by simp
            qed

            ultimately show "?Q ?recarg"
              using ih b by auto
          qed
          then show ?thesis
            by (simp add: b)
        qed
      qed
    qed
  }
  note dom=this
  from dom
  show "\<lbrakk> v \<in> vertices ; pre_dfs v e\<rbrakk> \<Longrightarrow> dfs_dfss_dom(Inl(v, e))"
    by auto
  from dom
  show "\<lbrakk> v \<in> vertices ; pre_dfss v e\<rbrakk> \<Longrightarrow> dfs_dfss_dom(Inr(v, e))"
    by auto
qed

text \<open>
  Putting everything together, we prove the total correctness of
  the algorithm when applied to some (root) vertex.
\<close>
theorem correctness:
  assumes "v \<in> vertices"
  shows "sccs (dfs v (init_env v)) = {S . is_scc S \<and> (\<forall>n\<in>S. reachable v n)}"
proof -
  have "pre_dfs v (init_env v)"
  by (auto simp: pre_dfs_def wf_env_def init_env_def is_subscc_def
           dest: precedes_mem)
  with assms show ?thesis
    by (simp add: dfs_dfss_termination partial_correctness)
qed


end
end
