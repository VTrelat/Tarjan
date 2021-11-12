theory Tarjan
imports Main
begin

text \<open>
  Tarjan's algorithm computes the strongly connected components of
  a finite graph using depth-first search. We formalize a functional
  version of the algorithm in Isabelle/HOL, following a development
  of Lévy et al. in Why3 that is available at
  \url{http://pauillac.inria.fr/~levy/why3/graph/abs/scct/1-68bis/scc.html}.
\<close>

text \<open>Make the simplifier expand let-constructions automatically\<close>
declare Let_def[simp]

text \<open>
  Definition of an auxiliary data structure holding local variables
  during the execution of Tarjan's algorithm.
\<close>
record 'v env =
  black :: "'v set"
  gray  :: "'v set"
  stack :: "'v list"
  sccs  :: "'v set set"
  sn    :: nat
  num   :: "'v \<Rightarrow> int"

definition colored where
  "colored e \<equiv> black e \<union> gray e"

locale graph =
  fixes vertices :: "'v set"
    and successors :: "'v \<Rightarrow> 'v set"
  assumes vfin: "finite vertices"
    and sclosed: "\<forall>x \<in> vertices. successors x \<subseteq> vertices"

context graph
begin

section {* Reachability in graphs *}

abbreviation edge where
  "edge x y \<equiv> y \<in> successors x"

definition xedge_to where
  \<comment> \<open>@{text ys} is a suffix of @{text xs}, @{text y} appears in @{text ys},
      and there is an edge from some node in the prefix of @{text xs} to @{text y}\<close>
  "xedge_to xs ys y \<equiv>
    y \<in> set ys
  \<and> (\<exists>zs. xs = zs @ ys \<and> (\<exists>z \<in> set zs. edge z y))"

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

text {*
  Given some set @{text S} and two vertices @{text x} and @{text y}
  such that @{text y} is reachable from @{text x}, and @{text x} is
  an element of @{text S} but @{text y} is not, then there exists
  some vertices @{text x'} and @{text y'} linked by an edge such that
  @{text x'} is an element of @{text S}, @{text y'} is not,
  @{text x'} is reachable from @{text x}, and @{text y} is reachable  
  from @{text y'}.
*}
lemma reachable_crossing_set:
  assumes 1: "reachable x y" and 2: "x \<in> S" and 3: "y \<notin> S"
  obtains x' y' where
    "x' \<in> S" "y' \<notin> S" "edge x' y'" "reachable x x'" "reachable y' y"
proof -
  from assms
  have "\<exists>x' y'. x' \<in> S \<and> y' \<notin> S \<and> edge x' y' \<and> reachable x x' \<and> reachable y' y"
    by induct (blast intro: reachable_edge reachable_trans)+
  with that show ?thesis by blast
qed

section {* Strongly connected components *}

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


section {* Auxiliary functions *}

abbreviation infty ("\<infinity>") where
  \<comment> \<open>integer exceeding any one used as a vertex number during the algorithm\<close>
  "\<infinity> \<equiv> int (card vertices)"

definition set_infty where
  \<comment> \<open>set @{text "f x"} to @{text \<infinity>} for all x in xs\<close>
  "set_infty xs f = fold (\<lambda>x g. g (x := \<infinity>)) xs f"

lemma set_infty:
  "(set_infty xs f) x = (if x \<in> set xs then \<infinity> else f x)"
  unfolding set_infty_def by (induct xs arbitrary: f) auto

text {*
  Split a list at the first occurrence of a given element.
  Returns the two sublists of elements before (and including)
  the element and those strictly after the element. 
  If the element does not occur in the list, returns a pair 
  formed by the entire list and the empty list.
*}
fun split_list where
  "split_list x []  = ([], [])"
| "split_list x (y # xs) =
    (if x = y then ([x], xs) else 
       (let (l, r) = split_list x xs in
         (y # l, r)))" 

lemma split_list_concat:
  \<comment> \<open>Concatenating the two sublists produced by @{text "split_list"}
      yields back the original list.\<close>
  assumes "x \<in> set xs"
  shows "(fst (split_list x xs)) @ (snd (split_list x xs)) = xs"
  using assms by (induct xs) (auto simp: split_def)

lemma fst_split_list:
  assumes "x \<in> set xs"
  shows "\<exists>ys. fst (split_list x xs) = ys @ [x] \<and> x \<notin> set ys"
  using assms by (induct xs) (auto simp: split_def)

text \<open>
  Push a vertex on the stack and increment the sequence number.
  The pushed vertex is associated with the (old) sequence number.
  It is also added to the set of gray nodes.
\<close>
definition add_stack_incr where
  "add_stack_incr x e =
      e \<lparr> gray := insert x (gray e),
          stack := x # (stack e),
          sn := sn e +1,
          num := (num e) (x := int (sn e)) \<rparr>"

text \<open>
  Add vertex @{text x} to the set of black vertices in @{text e}
  and remove it from the set of gray vertices.
\<close>
definition add_black where
  "add_black x e = e \<lparr> black := insert x (black e),
                       gray := (gray e) - {x} \<rparr>"


section \<open>Main functions used for Tarjan's algorithms\<close>

subsection \<open>Function definitions\<close>

text {*
  We define two mutually recursive functions that contain the essence
  of Tarjan's algorithm. Their arguments are respectively a single
  vertex and a set of vertices, as well as an environment that contains
  the local variables of the algorithm, and an auxiliary parameter
  representing the set of ``gray'' vertices, which is used only for
  the proof. The main function is then obtained by specializing the
  function operating on a set of vertices.
*}

function (domintros) dfs1 and dfs where
  "dfs1 x e  =
    (let (n1, e1) = dfs (successors x) (add_stack_incr x e) in
      if n1 < int (sn e) then (n1, add_black x e1)
      else
       (let (l,r) = split_list x (stack e1) in
         (\<infinity>, 
           \<lparr> black = insert x (black e1),
             gray = gray e,
             stack = r,
             sccs = insert (set l) (sccs e1),
             sn = sn e1,
             num = set_infty l (num e1) \<rparr> )))"
| "dfs roots e =
    (if roots = {} then (\<infinity>, e)
    else
      (let x = SOME x. x \<in> roots;
           res1 = (if num e x \<noteq> -1 then (num e x, e) else dfs1 x e);
           res2 = dfs (roots - {x}) (snd res1)
      in (min (fst res1) (fst res2), snd res2) ))"
  by pat_completeness auto

definition init_env where
  "init_env \<equiv> \<lparr> black = {},            gray = {},
                stack = [],            sccs = {},
                sn = 0,                num = \<lambda>_. -1 \<rparr>"

definition tarjan where
  "tarjan \<equiv> sccs (snd (dfs vertices init_env))"


subsection \<open>Well-definedness of the functions\<close>

text \<open>
  We did not prove termination when we defined the two mutually 
  recursive functions @{text dfs1} and @{text dfs} defined above,
  and indeed it is easy to see that they do not terminate for
  arbitrary arguments. Isabelle allows us to define ``partial''
  recursive functions, for which it introduces an auxiliary
  domain predicate that characterizes their domain of definition.
  We now make this more concrete and prove that the two functions
  terminate when called for nodes of the graph, also assuming an
  elementary well-definedness condition for environments. These
  conditions are met in the cases of interest, and in particular
  in the call to @{text dfs} in the main function @{text tarjan}.
  Intuitively, the reason is that every (possibly indirect)
  recursive call to @{text dfs} either decreases the set of roots
  or increases the set of nodes colored black or gray.
\<close>

text \<open>
  The set of nodes colored black never decreases in the course
  of the computation.
\<close>
lemma black_increasing:
  "dfs1_dfs_dom (Inl (x,e)) \<Longrightarrow> black e \<subseteq> black (snd (dfs1 x e))"
  "dfs1_dfs_dom (Inr (roots,e)) \<Longrightarrow> black e \<subseteq> black (snd (dfs roots e))"
  by (induct rule: dfs1_dfs.pinduct,
      (fastforce simp: dfs1.psimps dfs.psimps case_prod_beta 
                   add_black_def add_stack_incr_def)+)

text \<open>
  Similarly, the set of nodes colored black or gray 
  never decreases in the course of the computation.
\<close>
lemma colored_increasing:
  "dfs1_dfs_dom (Inl (x,e)) \<Longrightarrow>
    colored e \<subseteq> colored (snd (dfs1 x e)) \<and>
    colored (add_stack_incr x e)
    \<subseteq> colored (snd (dfs (successors x) (add_stack_incr x e)))"
  "dfs1_dfs_dom (Inr (roots,e)) \<Longrightarrow>
    colored e \<subseteq> colored (snd (dfs roots e))"
proof (induct rule: dfs1_dfs.pinduct)
  case (1 x e)
  from `dfs1_dfs_dom (Inl (x,e))`
  have "black e \<subseteq> black (snd (dfs1 x e))"
    by (rule black_increasing)
  with 1 show ?case
    by (auto simp: dfs1.psimps case_prod_beta add_stack_incr_def
                   add_black_def colored_def)
next
  case (2 roots e) then show ?case
    by (fastforce simp: dfs.psimps case_prod_beta)
qed

text \<open>
  The functions @{text dfs1} and @{text dfs} never assign the
  number of a vertex to -1.
\<close>
lemma dfs_num_defined:
  "\<lbrakk>dfs1_dfs_dom (Inl (x,e)); num (snd (dfs1 x e)) v = -1\<rbrakk> \<Longrightarrow>
    num e v = -1"
  "\<lbrakk>dfs1_dfs_dom (Inr (roots,e)); num (snd (dfs roots e)) v = -1\<rbrakk> \<Longrightarrow>
    num e v = -1"
  by (induct rule: dfs1_dfs.pinduct,
      (auto simp: dfs1.psimps dfs.psimps case_prod_beta add_stack_incr_def 
                  add_black_def set_infty
            split: if_split_asm))

text \<open>
  We are only interested in environments that assign positive
  numbers to colored nodes, and we show that calls to @{text dfs1}
  and @{text dfs} preserve this property.
\<close>
definition colored_num where
  "colored_num e \<equiv> \<forall>v \<in> colored e. v \<in> vertices \<and> num e v \<noteq> -1"

lemma colored_num:
  "\<lbrakk>dfs1_dfs_dom (Inl (x,e)); x \<in> vertices; colored_num e\<rbrakk> \<Longrightarrow>
    colored_num (snd (dfs1 x e))"
  "\<lbrakk>dfs1_dfs_dom (Inr (roots,e)); roots \<subseteq> vertices; colored_num e\<rbrakk> \<Longrightarrow>
    colored_num (snd (dfs roots e))"
proof (induct rule: dfs1_dfs.pinduct)
  case (1 x e) 
  let ?rec = "dfs (successors x) (add_stack_incr x e)"
  from sclosed `x \<in> vertices`
  have "successors x \<subseteq> vertices" ..
  moreover
  from `colored_num e` `x \<in> vertices`
  have "colored_num (add_stack_incr x e)" 
    by (auto simp: colored_num_def add_stack_incr_def colored_def)
  ultimately 
  have rec: "colored_num (snd ?rec)"
    using 1 by blast
  have x: "x \<in> colored (add_stack_incr x e)"
    by (simp add: add_stack_incr_def colored_def)
  from `dfs1_dfs_dom (Inl (x,e))` colored_increasing
  have colrec: "colored (add_stack_incr x e) \<subseteq> colored (snd ?rec)"
    by blast
  show ?case
  proof (cases "fst ?rec < int (sn e)")
    case True
    with rec x colrec `dfs1_dfs_dom (Inl (x,e))` show ?thesis
      by (auto simp: dfs1.psimps case_prod_beta 
                     colored_num_def add_black_def colored_def)
  next
    case False
    let ?e' = "snd (dfs1 x e)"
    have "colored e \<subseteq> colored (add_stack_incr x e)"
      by (auto simp: colored_def add_stack_incr_def)
    with False x colrec `dfs1_dfs_dom (Inl (x,e))`
    have "colored ?e' \<subseteq> colored (snd ?rec)" 
         "\<exists>xs. num ?e' = set_infty xs (num (snd ?rec))"
      by (auto simp: dfs1.psimps case_prod_beta colored_def)
    with rec show ?thesis
      by (auto simp: colored_num_def set_infty split: if_split_asm)
  qed
next
  case (2 roots e)
  show ?case
  proof (cases "roots = {}")
    case True
    with `dfs1_dfs_dom (Inr (roots,e))` `colored_num e`
    show ?thesis by (auto simp: dfs.psimps)
  next
    case False
    let ?x = "SOME x. x \<in> roots"
    from False obtain r where "r \<in> roots" by blast
    hence "?x \<in> roots" by (rule someI)
    with `roots \<subseteq> vertices` have x: "?x \<in> vertices" ..
    let ?res1 = "if num e ?x \<noteq> -1 then (num e ?x, e) else dfs1 ?x e"
    let ?res2 = "dfs (roots - {?x}) (snd ?res1)"
    from 2 False `roots \<subseteq> vertices` x
    have "colored_num (snd ?res1)" by auto
    with 2 False `roots \<subseteq> vertices`
    have "colored_num (snd ?res2)"
      by blast
    moreover
    from False `dfs1_dfs_dom (Inr (roots,e))`
    have "dfs roots e = (min (fst ?res1) (fst ?res2), snd ?res2)"
      by (auto simp: dfs.psimps)
    ultimately show ?thesis by simp
  qed
qed

text \<open>
  The following relation underlies the termination argument used
  for proving well-definedness of the functions @{text dfs1} and
  @{text dfs}. It is defined on the disjoint sum of the types of
  arguments of the two functions and relates the arguments of
  (mutually) recursive calls.
\<close>
definition dfs1_dfs_term where
  "dfs1_dfs_term \<equiv>
    { (Inl(x, e::'v env), Inr(roots,e)) | 
      x e roots .
      roots \<subseteq> vertices \<and> x \<in> roots \<and> colored e \<subseteq> vertices }
  \<union> { (Inr(roots, add_stack_incr x e), Inl(x, e)) |
      x e roots .
      colored e \<subseteq> vertices \<and> x \<in> vertices - colored e }
  \<union> { (Inr(roots, e::'v env), Inr(roots', e')) | 
      roots roots' e e' .
      roots' \<subseteq> vertices \<and> roots \<subset> roots' \<and> 
      colored e' \<subseteq> colored e \<and> colored e \<subseteq> vertices }"

text \<open>
  In order to prove that the above relation is well-founded, we
  use the following function that embeds it into triples whose first
  component is the complement of the colored nodes, whose second
  component is the set of root nodes, and whose third component
  is 1 or 2 depending on the function being called. The third
  component corresponds to the first case in the definition of
  @{text dfs1_dfs_term}.
\<close>
fun dfs1_dfs_to_tuple where
  "dfs1_dfs_to_tuple (Inl(x::'v, e::'v env)) = (vertices - colored e, {x}, 1::nat)"
| "dfs1_dfs_to_tuple (Inr(roots, e::'v env)) = (vertices - colored e, roots, 2)"

lemma wf_term: "wf dfs1_dfs_term"
proof -
  let ?r = "(finite_psubset :: ('v set \<times> 'v set) set)
            <*lex*> (finite_psubset :: ('v set \<times> 'v set) set)
            <*lex*> pred_nat"
  have "wf ?r"
    using wf_finite_psubset wf_pred_nat by blast
  moreover
  have "dfs1_dfs_term \<subseteq> inv_image ?r dfs1_dfs_to_tuple"
    unfolding dfs1_dfs_term_def pred_nat_def using vfin 
    by (auto dest: finite_subset simp: add_stack_incr_def colored_def)
  ultimately show ?thesis
    using wf_inv_image wf_subset by blast
qed

text \<open>
  The following theorem establishes sufficient conditions under
  which the two functions @{text dfs1} and @{text dfs} terminate.
  The proof proceeds by well-founded induction using the relation
  @{text dfs1_dfs_term} and makes use of the theorem
  @{text dfs1_dfs.domintros} that was generated by Isabelle from
  the mutually recursive definitions in order to characterize the
  domain conditions for these functions.
\<close>
theorem dfs1_dfs_termination:
  "\<lbrakk>x \<in> vertices - colored e; colored_num e\<rbrakk> \<Longrightarrow> dfs1_dfs_dom (Inl(x, e))"
  "\<lbrakk>roots \<subseteq> vertices; colored_num e\<rbrakk> \<Longrightarrow> dfs1_dfs_dom (Inr(roots, e))"
proof -
  { fix args
    have "(case args
          of Inl(x,e) \<Rightarrow> 
             x \<in> vertices - colored e \<and> colored_num e
          |  Inr(roots,e) \<Rightarrow> 
             roots \<subseteq> vertices \<and> colored_num e)
        \<longrightarrow> dfs1_dfs_dom args" (is "?P args \<longrightarrow> ?Q args")
    proof (rule wf_induct[OF wf_term])
      fix arg :: "('v \<times> 'v env) + ('v set \<times> 'v env)"
      assume ih: "\<forall>arg'. (arg',arg) \<in> dfs1_dfs_term
                      \<longrightarrow> (?P arg' \<longrightarrow> ?Q arg')"
      show "?P arg \<longrightarrow> ?Q arg"
      proof
        assume P: "?P arg"
        show "?Q arg"
        proof (cases arg)
          case (Inl a)
          then obtain x e where a: "arg = Inl(x,e)"
            using dfs1.cases by metis
          have "?Q (Inl(x,e))"
          proof (rule dfs1_dfs.domintros)
            let ?recarg = "Inr (successors x, add_stack_incr x e)"
            from a P have "(?recarg, arg) \<in> dfs1_dfs_term"
              by (auto simp: add_stack_incr_def colored_num_def dfs1_dfs_term_def)
            moreover
            from a P sclosed have "?P ?recarg"
              by (auto simp: add_stack_incr_def colored_num_def colored_def)
            ultimately show "?Q ?recarg"
              using ih by auto
          qed
          with a show ?thesis by simp
        next
          case (Inr b)
          then obtain roots e where b: "arg = Inr(roots,e)"
            using dfs.cases by metis
          let ?sx = "SOME x. x \<in> roots"
          let ?rec1arg = "Inl (?sx, e)"
          let ?rec2arg = "Inr (roots - {?sx}, e)"
          let ?rec3arg = "Inr (roots - {?sx}, snd (dfs1 ?sx e))"
          have "?Q (Inr(roots,e))"
          proof (rule dfs1_dfs.domintros)
            fix x
            assume 1: "x \<in> roots"
               and 2: "num e ?sx = -1"
               and 3: "\<not> dfs1_dfs_dom ?rec1arg"
            from 1 have sx: "?sx \<in> roots" by (rule someI)
            with P b have "(?rec1arg, arg) \<in> dfs1_dfs_term"
              by (auto simp: dfs1_dfs_term_def colored_num_def)
            moreover
            from sx 2 P b have "?P ?rec1arg"
              by (auto simp: colored_num_def)
            ultimately show False
              using ih 3 by auto
          next
            fix x
            assume "x \<in> roots"
            hence sx: "?sx \<in> roots" by (rule someI)
            from sx b P have "(?rec2arg, arg) \<in> dfs1_dfs_term"
              by (auto simp: dfs1_dfs_term_def colored_num_def)
            moreover
            from P b have "?P ?rec2arg" by auto
            ultimately show "dfs1_dfs_dom ?rec2arg"
              using ih by auto
          next
            fix x
            assume 1: "x \<in> roots" and 2: "num e ?sx = -1"
            from 1 have sx: "?sx \<in> roots" by (rule someI)
            have "dfs1_dfs_dom ?rec1arg"
            proof -
              from sx P b have "(?rec1arg, arg) \<in> dfs1_dfs_term"
                by (auto simp: dfs1_dfs_term_def colored_num_def)
              moreover
              from sx 2 P b have "?P ?rec1arg"
                by (auto simp: colored_num_def)
              ultimately show ?thesis
                using ih by auto
            qed
            with P b sx have "colored_num (snd (dfs1 ?sx e))"
              by (auto elim: colored_num)
            moreover
            from this sx b P `dfs1_dfs_dom ?rec1arg`
            have "(?rec3arg, arg) \<in> dfs1_dfs_term"
              by (auto simp: dfs1_dfs_term_def colored_num_def 
                       dest: colored_increasing)
            moreover
            from this P b `colored_num (snd (dfs1 ?sx e))`
            have "?P ?rec3arg" by auto
            ultimately show "dfs1_dfs_dom ?rec3arg"
              using ih by auto
          qed
          with b show ?thesis by simp
        qed
      qed
    qed
  }
  note dom = this
  from dom 
  show "\<lbrakk>x \<in> vertices - colored e; colored_num e\<rbrakk> \<Longrightarrow> dfs1_dfs_dom (Inl(x,e))"
    by auto
  from dom
  show "\<lbrakk>roots \<subseteq> vertices; colored_num e\<rbrakk> \<Longrightarrow> dfs1_dfs_dom (Inr(roots,e))"
    by auto
qed


section {* Auxiliary notions for the proof of partial correctness *}

text \<open>
  The proof of partial correctness is more challenging and requires
  some further concepts that we now define.

  We need to reason about the relative order of elements in a list
  (specifically, the stack used in the algorithm).
\<close>
definition precedes ("_ \<preceq> _ in _" [100,100,100] 39) where
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


section {* Predicates and lemmas about environments *}

definition subenv where
  "subenv e e' \<equiv>
    (\<exists>s. stack e' = s @ (stack e) \<and> set s \<subseteq> black e')
  \<and> black e \<subseteq> black e' \<and> gray e = gray e'
  \<and> sccs e \<subseteq> sccs e'
  \<and> (\<forall>x \<in> set (stack e). num e x = num e' x)"

lemma subenv_refl [simp]: "subenv e e"
  by (auto simp: subenv_def)

lemma subenv_trans:
  assumes "subenv e e'" and "subenv e' e''"
  shows "subenv e e''"
  using assms unfolding subenv_def by force

definition wf_color where
  \<comment> \<open>conditions about colors, part of the invariant of the algorithm\<close>
  "wf_color e \<equiv>
    colored e \<subseteq> vertices
  \<and> black e \<inter> gray e = {}
  \<and> (\<Union> sccs e) \<subseteq> black e
  \<and> set (stack e) = gray e \<union> (black e - \<Union> sccs e)"

definition wf_num where
  \<comment> \<open>conditions about vertex numbers\<close>
  "wf_num e \<equiv>
    int (sn e) \<le> \<infinity>
  \<and> (\<forall>x. -1 \<le> num e x \<and> (num e x = \<infinity> \<or> num e x < int (sn e)))
  \<and> sn e = card (colored e)
  \<and> (\<forall>x. num e x = \<infinity> \<longleftrightarrow> x \<in> \<Union> sccs e)
  \<and> (\<forall>x. num e x = -1 \<longleftrightarrow> x \<notin> colored e)
  \<and> (\<forall>x \<in> set (stack e). \<forall>y \<in> set (stack e).
        (num e x \<le> num e y \<longleftrightarrow> y \<preceq> x in (stack e)))"

lemma subenv_num:
  \<comment> \<open>If @{text e} and @{text e'} are two well-formed environments,
      and @{text e} is a sub-environment of @{text e'} then the number
      assigned by @{text e'} to any vertex is at least that assigned
      by @{text e}.\<close>
  assumes sub: "subenv e e'"
      and e: "wf_color e" "wf_num e"
      and e': "wf_color e'" "wf_num e'"
  shows "num e x \<le> num e' x"
(*
  using assms unfolding wf_color_def wf_num_def subenv_def colored_def
  by (smt DiffI UnCI UnE mem_simps(9) subsetCE)
*)
proof (cases "x \<in> colored e")
  case True then show ?thesis unfolding colored_def
  proof
    assume "x \<in> gray e"
    with e sub show ?thesis 
      by (auto simp: wf_color_def subenv_def)
  next
    assume "x \<in> black e"
    show ?thesis
    proof (cases "x \<in> \<Union> sccs e")
      case True
      with sub e e' have "num e x = \<infinity>" "num e' x = \<infinity>"
        by (auto simp: subenv_def wf_num_def)
      thus ?thesis by simp
    next
      case False
      with \<open>x \<in> black e\<close> e sub show ?thesis
        by (auto simp: wf_color_def subenv_def)
    qed
  qed
next
  case False with e e' show ?thesis
    unfolding wf_num_def by metis
qed

definition no_black_to_white where
  \<comment> \<open>successors of black vertices cannot be white\<close>
  "no_black_to_white e \<equiv> \<forall>x y. edge x y \<and> x \<in> black e \<longrightarrow> y \<in> colored e"

definition wf_env where
  "wf_env e \<equiv>
    wf_color e \<and> wf_num e
  \<and> no_black_to_white e \<and> distinct (stack e)
  \<and> (\<forall>x y. y \<preceq> x in (stack e) \<longrightarrow> reachable x y)
  \<and> (\<forall>y \<in> set (stack e). \<exists>g \<in> gray e. y \<preceq> g in (stack e) \<and> reachable y g)
  \<and> sccs e = { C . C \<subseteq> black e \<and> is_scc C }"

lemma num_in_stack:
  assumes "wf_env e" and "x \<in> set (stack e)"
  shows "num e x \<noteq> -1"
        "num e x < int (sn e)"
proof -
  from assms 
  show "num e x \<noteq> -1"
    by (auto simp: wf_env_def wf_color_def wf_num_def colored_def)
  from `wf_env e`
  have "num e x < int (sn e) \<or> x \<in> \<Union> sccs e"
    unfolding wf_env_def wf_num_def by metis
  with assms show "num e x < int (sn e)"
    unfolding wf_env_def wf_color_def by blast
qed

text \<open>
  Numbers assigned to different stack elements are distinct.
\<close>
lemma num_inj:
  assumes "wf_env e" and "x \<in> set (stack e)" 
      and "y \<in> set (stack e)" and "num e x = num e y"
    shows "x = y"
  using assms unfolding wf_env_def wf_num_def
  by (metis precedes_refl precedes_antisym) 

text \<open>
  The set of black elements at the top of the stack together
  with the first gray element always form a sub-SCC. This lemma
  is useful for the ``else'' branch of @{text dfs1}.
\<close>
lemma first_gray_yields_subscc:
  assumes e: "wf_env e"
    and x: "stack e = ys @ (x # zs)"
    and g: "x \<in> gray e"
    and ys: "set ys \<subseteq> black e"
  shows "is_subscc (insert x (set ys))"
proof -
  from e x have "\<forall>y \<in> set ys. \<exists>g \<in> gray e. reachable y g"
    unfolding wf_env_def by force
  moreover
  have "\<forall>g \<in> gray e. reachable g x"
  proof
    fix g
    assume "g \<in> gray e"
    with e x ys have "g \<in> set (x # zs)"
      unfolding wf_env_def wf_color_def by auto
    with e x show "reachable g x"
      unfolding wf_env_def precedes_def by blast
  qed
  moreover
  from e x g have "\<forall>y \<in> set ys. reachable x y"
    unfolding wf_env_def by (simp add: split_list_precedes)
  ultimately show ?thesis
    unfolding is_subscc_def 
    by (metis reachable_trans reachable_refl insertE)
qed

section \<open>Partial correctness of the main functions\<close>

text \<open>
  We now define the pre- and post-conditions for proving that
  the functions @{text dfs1} and @{text dfs} are partially correct.
  The parameters of the preconditions, as well as the first parameters
  of the postconditions, coincide with the parameters of the
  functions @{text dfs1} and @{text dfs}. The final parameter of
  the postconditions represents the result computed by the function.
\<close>

definition dfs1_pre where
  "dfs1_pre x e \<equiv>
    x \<in> vertices
  \<and> x \<notin> colored e
  \<and> (\<forall>g \<in> gray e. reachable g x)
  \<and> wf_env e"

definition dfs1_post where
  "dfs1_post x e res \<equiv>
    let n = fst res; e' = snd res
    in  wf_env e'
      \<and> subenv e e'
      \<and> x \<in> black e'
      \<and> n \<le> num e' x
      \<and> (n = \<infinity> \<or> (\<exists>y \<in> set (stack e'). num e' y = n \<and> reachable x y))
      \<and> (\<forall>y. xedge_to (stack e') (stack e) y \<longrightarrow> n \<le> num e' y)"

definition dfs_pre where
  "dfs_pre roots e \<equiv>
    roots \<subseteq> vertices
  \<and> (\<forall>x \<in> roots. \<forall>g \<in> gray e. reachable g x)
  \<and> wf_env e"

definition dfs_post where
  "dfs_post roots e res \<equiv>
    let n = fst res; e' = snd res
    in  wf_env e'
      \<and> subenv e e'
      \<and> roots \<subseteq> colored e'
      \<and> (\<forall>x \<in> roots. n \<le> num e' x)
      \<and> (n = \<infinity> \<or> (\<exists>x \<in> roots. \<exists>y \<in> set (stack e'). num e' y = n \<and> reachable x y))
      \<and> (\<forall>y. xedge_to (stack e') (stack e) y \<longrightarrow> n \<le> num e' y)"

text \<open>
  The following lemmas express some useful consequences of the
  pre- and post-conditions. In particular, the preconditions
  ensure that the function calls terminate.
\<close>

lemma dfs1_pre_domain:
  assumes "dfs1_pre x e"
  shows "colored e \<subseteq> vertices" 
        "x \<in> vertices - colored e"
        "x \<notin> set (stack e)"
        "int (sn e) < \<infinity>"
  using assms vfin
  unfolding dfs1_pre_def wf_env_def wf_color_def wf_num_def colored_def
  by (auto intro: psubset_card_mono)

lemma dfs1_pre_dfs1_dom:
  "dfs1_pre x e \<Longrightarrow> dfs1_dfs_dom (Inl(x,e))"
  unfolding dfs1_pre_def wf_env_def wf_color_def wf_num_def
  by (auto simp: colored_num_def intro!: dfs1_dfs_termination)

lemma dfs_pre_dfs_dom:
  "dfs_pre roots e \<Longrightarrow> dfs1_dfs_dom (Inr(roots,e))"
  unfolding dfs_pre_def wf_env_def wf_color_def wf_num_def
  by (auto simp: colored_num_def intro!: dfs1_dfs_termination)

(** not needed, but potentially useful
lemma dfs1_post_num:
  "dfs1_post x e res \<Longrightarrow> fst res \<le> \<infinity>"
  unfolding dfs1_post_def wf_env_def wf_num_def
  by smt

lemma dfs_post_num:
  "dfs_post roots e res \<Longrightarrow> fst res \<le> \<infinity>"
  unfolding dfs_post_def wf_env_def wf_num_def
  by smt
**)

lemma dfs_post_stack:
  assumes "dfs_post roots e res"
  obtains s where 
    "stack (snd res) = s @ stack e" 
    "set s \<subseteq> black (snd res)"
    "\<forall>x \<in> set (stack e). num (snd res) x = num e x"
  using assms unfolding dfs_post_def subenv_def by auto

lemma dfs_post_split:
  fixes x e res
  defines "n' \<equiv> fst res"
  defines "e' \<equiv> snd res"
  defines "l \<equiv> fst (split_list x (stack e'))"
  defines "r \<equiv> snd (split_list x (stack e'))"
  assumes post: "dfs_post (successors x) (add_stack_incr x e) res"
             (is "dfs_post ?roots ?e res")
  obtains ys where
    "l = ys @ [x]"
    "x \<notin> set ys"
    "set ys \<subseteq> black e'"
    "stack e' = l @ r"
    "is_subscc (set l)"
    "r = stack e"
proof -
  from post have dist: "distinct (stack e')"
    unfolding dfs_post_def wf_env_def e'_def by auto
  from post obtain s where
    s: "stack e' = s @ (x # stack e)" "set s \<subseteq> black e'"
    unfolding add_stack_incr_def e'_def
    by (auto intro: dfs_post_stack)
  then obtain ys where ys: "l = ys @ [x]" "x \<notin> set ys" "stack e' = l @ r"
    unfolding add_stack_incr_def l_def r_def
    by (metis in_set_conv_decomp split_list_concat fst_split_list)
  with s have l: "l = (s @ [x]) \<and> r = stack e"
    by (metis dist append.assoc append.simps(1) append.simps(2) 
              append_Cons_eq_iff distinct.simps(2) distinct_append)
  from post have "wf_env e'" "x \<in> gray e'"
    by (auto simp: dfs_post_def subenv_def add_stack_incr_def e'_def)
  with s l have "is_subscc (set l)"
    by (auto simp: add_stack_incr_def intro: first_gray_yields_subscc)
  with s ys l that show ?thesis by auto
qed

text {*
  A crucial lemma establishing a condition after the ``then'' branch
  following the recursive call in function @{text dfs1}.
*}
lemma dfs_post_reach_gray:
  fixes x e res
  defines "n' \<equiv> fst res"
  defines "e' \<equiv> snd res"
  assumes e: "wf_env e"
      and post: "dfs_post (successors x) (add_stack_incr x e) res"
             (is "dfs_post ?roots ?e res")
      and n': "n' < int (sn e)"
  obtains g where
    "g \<noteq> x" "g \<in> gray e'" "x \<preceq> g in (stack e')" 
    "reachable x g" "reachable g x"
proof -
  from post have e': "wf_env e'" "subenv ?e e'"
    by (auto simp: dfs_post_def e'_def)
  hence x_e': "x \<in> set (stack e')" "x \<in> vertices" "num e' x = int(sn e)"
    by (auto simp: add_stack_incr_def subenv_def wf_env_def wf_color_def colored_def)
  from e n' have "n' \<noteq> \<infinity>"
    unfolding wf_env_def wf_num_def by simp
  with post e' obtain sx y g where
    g: "sx \<in> ?roots" "y \<in> set (stack e')" "num e' y = n'" "reachable sx y"
       "g \<in> gray e'" "g \<in> set (stack e')" "y \<preceq> g in (stack e')" "reachable y g"
    unfolding dfs_post_def e'_def n'_def wf_env_def
    by (fastforce intro: precedes_mem )
  with e' have "num e' g \<le> num e' y"
    unfolding wf_env_def wf_num_def by metis
  with n' x_e' \<open>num e' y = n'\<close> 
  have "num e' g \<le> num e' x" "g \<noteq> x" by auto
  with \<open>g \<in> set (stack e')\<close> \<open>x \<in> set (stack e')\<close> e'
  have "g \<noteq> x \<and> x \<preceq> g in (stack e') \<and> reachable g x"
    unfolding wf_env_def wf_num_def by auto
  moreover 
  from g have "reachable x g"
    by (metis reachable_succ reachable_trans)
  moreover
  note \<open>g \<in> gray e'\<close> that
  ultimately show ?thesis by auto
qed

text {*
  The following lemmas represent steps in the proof of partial correctness.
*}

lemma dfs1_pre_dfs_pre:
  \<comment> \<open>The precondition of @{text dfs1} establishes that of the recursive
      call to @{text dfs}.\<close>
  assumes "dfs1_pre x e"
  shows "dfs_pre (successors x) (add_stack_incr x e)"
        (is "dfs_pre ?roots' ?e'")
proof -
  from assms sclosed have "?roots' \<subseteq> vertices"
    unfolding dfs1_pre_def by blast
  moreover
  from assms have "\<forall>y \<in> ?roots'. \<forall>g \<in> gray ?e'. reachable g y"
    unfolding dfs1_pre_def add_stack_incr_def
    by (auto dest: succ_reachable reachable_trans)
  moreover
  {
    from assms have wf_col': "wf_color ?e'"
      by (auto simp: dfs1_pre_def wf_env_def wf_color_def 
                     add_stack_incr_def colored_def)
    note 1 = dfs1_pre_domain[OF assms]
    from assms 1 have dist': "distinct (stack ?e')"
      unfolding dfs1_pre_def wf_env_def add_stack_incr_def by auto
    from assms have 3: "sn e = card (colored e)"
      unfolding dfs1_pre_def wf_env_def wf_num_def by simp
    from 1 have 4: "int (sn ?e') \<le> \<infinity>"
      unfolding add_stack_incr_def by simp
    with assms have 5: "\<forall>x. -1 \<le> num ?e' x \<and> (num ?e' x = \<infinity> \<or> num ?e' x < int (sn ?e'))"
      unfolding dfs1_pre_def wf_env_def wf_num_def add_stack_incr_def by auto
    from 1 vfin have "finite (colored e)" using finite_subset by blast
    with 1 3 have 6: "sn ?e' = card (colored ?e')"
      unfolding add_stack_incr_def colored_def by auto
    from assms 1 3 have 7: "\<forall>y. num ?e' y = \<infinity> \<longleftrightarrow> y \<in> \<Union> sccs ?e'"
      by (auto simp: dfs1_pre_def wf_env_def wf_num_def
                     add_stack_incr_def colored_def)
    from assms 3 have 8: "\<forall>y. num ?e' y = -1 \<longleftrightarrow> y \<notin> colored ?e'"
      by (auto simp: dfs1_pre_def wf_env_def wf_num_def add_stack_incr_def colored_def)
    from assms 1 have "\<forall>y \<in> set (stack e). num ?e' y < num ?e' x"
      unfolding dfs1_pre_def add_stack_incr_def
      by (auto dest: num_in_stack)
    moreover
    have "\<forall>y \<in> set (stack e). x \<preceq> y in (stack ?e')"
      unfolding add_stack_incr_def by (auto intro: head_precedes)
    moreover
    from 1 have "\<forall>y \<in> set (stack e). \<not>(y \<preceq> x in (stack ?e'))"
      unfolding add_stack_incr_def by (auto dest: tail_not_precedes)
    moreover
    {
      fix y z
      assume "y \<in> set (stack e)" "z \<in> set (stack e)"
      with 1 have "x \<noteq> y" by auto
      hence "y \<preceq> z in (stack ?e') \<longleftrightarrow> y \<preceq> z in (stack e)"
        by (simp add: add_stack_incr_def precedes_in_tail)
    }
    ultimately
    have 9: "\<forall>y \<in> set (stack ?e'). \<forall>z \<in> set (stack ?e').
                num ?e' y \<le> num ?e' z \<longleftrightarrow> z \<preceq> y in (stack ?e')"
      using assms
      unfolding dfs1_pre_def wf_env_def wf_num_def add_stack_incr_def
      by auto
    from 4 5 6 7 8 9 have wf_num': "wf_num ?e'"
      unfolding wf_num_def by blast
    from assms have nbtw': "no_black_to_white ?e'"
      by (auto simp: dfs1_pre_def wf_env_def no_black_to_white_def 
                     add_stack_incr_def colored_def)

    have stg': "\<forall>y \<in> set (stack ?e'). \<exists>g \<in> gray ?e'.
                   y \<preceq> g in (stack ?e') \<and> reachable y g"
    proof
      fix y
      assume y: "y \<in> set (stack ?e')"
      show "\<exists>g \<in> gray ?e'. y \<preceq> g in (stack ?e') \<and> reachable y g"
      proof (cases "y = x")
        case True
        then show ?thesis
          unfolding add_stack_incr_def by auto
      next
        case False
        with y have "y \<in> set (stack e)"
          by (simp add: add_stack_incr_def)
        with assms obtain g where 
          "g \<in> gray e \<and> y \<preceq> g in (stack e) \<and> reachable y g"
          unfolding dfs1_pre_def wf_env_def by blast
        thus ?thesis
          unfolding add_stack_incr_def
          by (auto dest: precedes_append_left[where ys="[x]"])
      qed
    qed

    have str': "\<forall>y z. y \<preceq> z in (stack ?e') \<longrightarrow> reachable z y"
    proof (clarify)
      fix y z
      assume yz: "y \<preceq> z in stack ?e'"
      show "reachable z y"
      proof (cases "y = x")
        case True
        from yz[THEN precedes_mem(2)] stg'
        obtain g where "g \<in> gray ?e'" "reachable z g" by blast
        with True assms show ?thesis
          unfolding dfs1_pre_def add_stack_incr_def
          by (auto elim: reachable_trans)
      next
        case False
        with yz have yze: "y \<preceq> z in stack e"
          by (simp add: add_stack_incr_def precedes_in_tail)
        with assms show ?thesis
          unfolding dfs1_pre_def wf_env_def by blast
      qed
    qed
    from assms have "sccs (add_stack_incr x e) = 
           {C . C \<subseteq> black (add_stack_incr x e) \<and> is_scc C}"
      by (auto simp: dfs1_pre_def wf_env_def add_stack_incr_def)
    with wf_col' wf_num' nbtw' dist' str' stg'
    have "wf_env ?e'"
      unfolding wf_env_def by blast
  }
  ultimately show ?thesis
    unfolding dfs_pre_def by blast
qed

lemma dfs_pre_dfs1_pre:
  \<comment> \<open>The precondition of @{text dfs} establishes that of the recursive
      call to @{text dfs1}, for any @{text "x \<in> roots"} such that
      @{text "num e x = -1"}.\<close>
  assumes "dfs_pre roots e" and "x \<in> roots" and "num e x = -1"
  shows "dfs1_pre x e"
  using assms unfolding dfs_pre_def dfs1_pre_def wf_env_def wf_num_def by auto

text \<open>
  Prove the post-condition of @{text dfs1} for the ``then'' branch
  in the definition of @{text dfs1}, assuming that the recursive call
  to @{text dfs} establishes its post-condition.
\<close>
lemma dfs_post_dfs1_post_case1:
  fixes x e
  defines "res1 \<equiv> dfs (successors x) (add_stack_incr x e)"
  defines "n1 \<equiv> fst res1"
  defines "e1 \<equiv> snd res1"
  defines "res \<equiv> dfs1 x e"
  assumes pre: "dfs1_pre x e"
      and post: "dfs_post (successors x) (add_stack_incr x e) res1"
      and lt: "fst res1 < int (sn e)"
  shows "dfs1_post x e res"
proof -
  let ?e' = "add_black x e1"
  from pre have dom: "dfs1_dfs_dom (Inl (x, e))"
    by (rule dfs1_pre_dfs1_dom)
  from lt dom have dfs1: "res = (n1, ?e')"
    by (simp add: res1_def n1_def e1_def res_def case_prod_beta dfs1.psimps)
  from post have wf_env1: "wf_env e1"
    unfolding dfs_post_def e1_def by auto
  from post obtain s where s: "stack e1 = s @ stack (add_stack_incr x e)"
    unfolding e1_def by (blast intro: dfs_post_stack)
  from post have x_e1: "x \<in> set (stack e1)"
    by (auto intro: dfs_post_stack simp: e1_def add_stack_incr_def)
  from post have se1: "subenv (add_stack_incr x e) e1"
    unfolding dfs_post_def by (simp add: e1_def split_def)
  from pre lt post obtain g where
    g: "g \<noteq> x" "g \<in> gray e1" "x \<preceq> g in (stack e1)" 
       "reachable x g" "reachable g x"
    unfolding e1_def using dfs_post_reach_gray dfs1_pre_def by blast

  have wf_env': "wf_env ?e'"
  proof -
    from wf_env1 dfs1_pre_domain[OF pre] x_e1 have "wf_color ?e'"
      by (auto simp: dfs_pre_def wf_env_def wf_color_def add_black_def colored_def)
    moreover
    from se1
    have "x \<in> gray e1" "colored ?e' = colored e1"
      by (auto simp: subenv_def add_stack_incr_def add_black_def colored_def)
    with wf_env1 have "wf_num ?e'"
      unfolding dfs_pre_def wf_env_def wf_num_def add_black_def by auto
    moreover
    from post wf_env1 have "no_black_to_white ?e'"
      unfolding dfs_post_def wf_env_def no_black_to_white_def 
                add_black_def e1_def subenv_def colored_def
      by auto
    moreover
    {
      fix y
      assume "y \<in> set (stack ?e')"
      hence y: "y \<in> set (stack e1)" by (simp add: add_black_def)
      with wf_env1 obtain z where 
        z: "z \<in> gray e1"
           "y \<preceq> z in stack e1"
           "reachable y z"
        unfolding wf_env_def by blast
      have "\<exists>g \<in> gray ?e'.
             y \<preceq> g in (stack ?e') \<and> reachable y g"
      proof (cases "z \<in> gray ?e'")
        case True with z show ?thesis by (auto simp: add_black_def)
      next
        case False
        with z have "z = x" by (simp add: add_black_def)
        with g z wf_env1 show ?thesis
          unfolding wf_env_def add_black_def
          by (auto elim: reachable_trans precedes_trans)
      qed
    }
    moreover
    have "sccs ?e' = {C . C \<subseteq> black ?e' \<and> is_scc C}"
    proof -
      {
        fix C
        assume "C \<in> sccs ?e'"
        with post have "is_scc C \<and> C \<subseteq> black ?e'"
          unfolding dfs_post_def wf_env_def add_black_def e1_def by auto
      }
      moreover
      {
        fix C
        assume C: "is_scc C" "C \<subseteq> black ?e'"
        have "x \<notin> C"
        proof
          assume xC: "x \<in> C"
          with \<open>is_scc C\<close> g have "g \<in> C"
            unfolding is_scc_def by (auto dest: subscc_add)
          with wf_env1 g \<open>C \<subseteq> black ?e'\<close>  show "False"
            unfolding wf_env_def wf_color_def add_black_def by auto
        qed
        with post C have "C \<in> sccs ?e'"
          unfolding dfs_post_def wf_env_def add_black_def e1_def by auto
      }
      ultimately show ?thesis by blast
    qed

    ultimately show ?thesis  \<comment> \<open>the remaining conjuncts carry over trivially\<close>
      using wf_env1 unfolding wf_env_def add_black_def by auto
  qed

  from pre have "x \<notin> set (stack e)" "x \<notin> gray e"
    unfolding dfs1_pre_def wf_env_def wf_color_def colored_def by auto
  with se1 have subenv': "subenv e ?e'"
    unfolding subenv_def add_stack_incr_def add_black_def
    by (auto split: if_split_asm)

  have xblack': "x \<in> black ?e'"
    unfolding add_black_def by simp

  from lt have "n1 < num (add_stack_incr x e) x"
    unfolding add_stack_incr_def n1_def by simp
  also have "\<dots> = num e1 x"
    using se1 unfolding subenv_def add_stack_incr_def by auto
  finally have xnum': "n1 \<le> num ?e' x"
    unfolding add_black_def by simp

  from lt pre have "n1 \<noteq> \<infinity>"
    unfolding dfs1_pre_def wf_env_def wf_num_def n1_def by simp
  with post obtain sx y where
    "sx \<in> successors x" "y \<in> set (stack ?e')" "num ?e' y = n1" "reachable sx y"
    unfolding dfs_post_def add_black_def n1_def e1_def by auto
  with dfs1_pre_domain[OF pre] 
  have n1': "\<exists>y \<in> set (stack ?e'). num ?e' y = n1 \<and> reachable x y"
    by (auto intro: reachable_trans)

  {
    fix y
    assume "xedge_to (stack ?e') (stack e) y"
    then obtain zs z where
      y: "stack ?e' = zs @ (stack e)" "z \<in> set zs" "y \<in> set (stack e)" "edge z y"
      unfolding xedge_to_def by auto
    have "n1 \<le> num ?e' y"
    proof (cases "z=x")
      case True
      with \<open>edge z y\<close> post show ?thesis
        unfolding dfs_post_def add_black_def n1_def e1_def by auto
    next
      case False
      with s y have "xedge_to (stack e1) (stack (add_stack_incr x e)) y"
        unfolding xedge_to_def add_black_def add_stack_incr_def by auto
      with post show ?thesis
        unfolding dfs_post_def add_black_def n1_def e1_def by auto
    qed
  }

  with dfs1 wf_env' subenv' xblack' xnum' n1'
  show ?thesis unfolding dfs1_post_def by simp
qed

text \<open>
  Prove the post-condition of @{text dfs1} for the ``else'' branch
  in the definition of @{text dfs1}, assuming that the recursive call
  to @{text dfs} establishes its post-condition.
\<close>
lemma dfs_post_dfs1_post_case2:
  fixes x e
  defines "res1 \<equiv> dfs (successors x) (add_stack_incr x e)"
  defines "n1 \<equiv> fst res1"
  defines "e1 \<equiv> snd res1"
  defines "res \<equiv> dfs1 x e"
  assumes pre: "dfs1_pre x e"
      and post: "dfs_post (successors x) (add_stack_incr x e) res1"
      and nlt: "\<not>(n1 < int (sn e))"
  shows "dfs1_post x e res"
proof -
  let ?split = "split_list x (stack e1)"
  let ?e' = "\<lparr> black = insert x (black e1),
               gray = gray e,
               stack = snd ?split,
               sccs = insert (set (fst ?split)) (sccs e1),
               sn = sn e1,
               num = set_infty (fst ?split) (num e1) \<rparr>"
  from pre have dom: "dfs1_dfs_dom (Inl (x, e))"
    by (rule dfs1_pre_dfs1_dom)
  from dom nlt have res: "res = (\<infinity>, ?e')"
    by (simp add: res1_def n1_def e1_def res_def case_prod_beta dfs1.psimps)
  from post have wf_e1: "wf_env e1" "subenv (add_stack_incr x e) e1" 
                        "successors x \<subseteq> colored e1"
    by (auto simp: dfs_post_def e1_def)
  hence gray': "gray e1 = insert x (gray e)"
    by (auto simp: subenv_def add_stack_incr_def)
  from post obtain l where
    l: "fst ?split = l @ [x]"
       "x \<notin> set l"
       "set l \<subseteq> black e1"
       "stack e1 = fst ?split @ snd ?split"
       "is_subscc (set (fst ?split))"
       "snd ?split = stack e"
    unfolding e1_def by (blast intro: dfs_post_split)
  hence x: "x \<in> set (stack e1)" by auto
  from l have stack: "set (stack e) \<subseteq> set (stack e1)" by auto
  from wf_e1 l 
  have dist: "x \<notin> set l"    "x \<notin> set (stack e)" 
             "set l \<inter> set (stack e) = {}"   
             "set (fst ?split) \<inter> set (stack e) = {}"
    unfolding wf_env_def by auto
  with \<open>stack e1 = fst ?split @ snd ?split\<close> \<open>snd ?split = stack e\<close>
  have prec: "\<forall>y \<in> set (stack e). \<forall>z. y \<preceq> z in (stack e1) \<longleftrightarrow> y \<preceq> z in (stack e)"
    by (metis precedes_append_left_iff Int_iff empty_iff) 
  from post have numx: "num e1 x = int (sn e)"
    unfolding dfs_post_def subenv_def add_stack_incr_def e1_def by auto

  text \<open>
    All nodes contained in the same SCC as @{text x} are elements of 
    @{text "fst ?split"}. Therefore, @{text "set (fst ?split)"} constitutes an SCC.\<close>
  {
    fix y
    assume xy: "reachable x y" and yx: "reachable y x"
       and y: "y \<notin> set (fst ?split)"
    from l(1) have "x \<in> set (fst ?split)" by simp
    with xy y obtain x' y' where
      y': "reachable x x'" "edge x' y'" "reachable y' y"
          "x' \<in> set (fst ?split)" "y' \<notin> set (fst ?split)"
      using reachable_crossing_set by metis
    with wf_e1 l have "y' \<in> colored e1"
      unfolding wf_env_def no_black_to_white_def by auto
    from \<open>reachable x x'\<close> \<open>edge x' y'\<close> have "reachable x y'"
      using reachable_succ reachable_trans by blast
    moreover
    from \<open>reachable y' y\<close> \<open>reachable y x\<close> have "reachable y' x"
      by (rule reachable_trans)
    ultimately have "y' \<notin> \<Union> sccs e1"
      using wf_e1 gray'
      by (auto simp: wf_env_def wf_color_def dest: sccE) 
    with wf_e1 \<open>y' \<in> colored e1\<close> have y'e1: "y' \<in> set (stack e1)"
      unfolding wf_env_def wf_color_def e1_def colored_def by auto
    with y' l have y'e: "y' \<in> set (stack e)" by auto
    with y' post l have numy': "n1 \<le> num e1 y'"
      unfolding dfs_post_def e1_def n1_def xedge_to_def add_stack_incr_def
      by force
    with numx nlt have "num e1 x \<le> num e1 y'" by auto
    with y'e1 x wf_e1 have "y' \<preceq> x in stack e1"
      unfolding wf_env_def wf_num_def e1_def n1_def by auto
    with y'e have "y' \<preceq> x in stack e" by (auto simp: prec)
    with dist have "False" by (simp add: precedes_mem)
  }
  hence "\<forall>y. reachable x y \<and> reachable y x \<longrightarrow> y \<in> set (fst ?split)"
    by blast
  with l have scc: "is_scc (set (fst ?split))"
    by (simp add: is_scc_def is_subscc_def subset_antisym subsetI)

  have wf_e': "wf_env ?e'"
  proof -
    have wfc: "wf_color ?e'"
    proof -
      from post dfs1_pre_domain[OF pre] l
      have "gray ?e' \<subseteq> vertices \<and> black ?e' \<subseteq> vertices 
           \<and> gray ?e' \<inter> black ?e' = {}
           \<and> (\<Union> sccs ?e') \<subseteq> black ?e'"
        by (auto simp: dfs_post_def wf_env_def wf_color_def e1_def subenv_def
                       add_stack_incr_def colored_def)
      moreover
      have "set (stack ?e') = gray ?e' \<union> (black ?e' - \<Union> sccs ?e')" (is "?lhs = ?rhs")
      proof
        from wf_e1 dist l show "?lhs \<subseteq> ?rhs"
          by (auto simp: wf_env_def wf_color_def e1_def subenv_def 
                         add_stack_incr_def colored_def)
      next
        from l have "stack ?e' = stack e" "gray ?e' = gray e" by simp+
        moreover
        from pre have "gray e \<subseteq> set (stack e)"
          unfolding dfs1_pre_def wf_env_def wf_color_def by auto
        moreover
        {
          fix v
          assume "v \<in> black ?e' - \<Union> sccs ?e'"
          with l wf_e1
          have "v \<in> black e1" "v \<notin> \<Union> sccs e1" "v \<notin> insert x (set l)" 
               "v \<in> set (stack e1)"
            unfolding wf_env_def wf_color_def by auto
          with l have "v \<in> set (stack e)" by auto
        }
        ultimately show "?rhs \<subseteq> ?lhs" by auto
      qed
      ultimately show ?thesis
        unfolding wf_color_def colored_def by blast
    qed
    moreover
    from wf_e1 l dist prec gray' have "wf_num ?e'"
      unfolding wf_env_def wf_num_def colored_def
      by (auto simp: set_infty)
    moreover 
    from wf_e1 gray' have "no_black_to_white ?e'"
      by (auto simp: wf_env_def no_black_to_white_def colored_def)
    moreover 
    from wf_e1 l have "distinct (stack ?e')"
      unfolding wf_env_def by auto
    moreover 
    from wf_e1 prec
    have "\<forall>y z. y \<preceq> z in (stack e) \<longrightarrow> reachable z y"
      unfolding wf_env_def by (metis precedes_mem(1))
    moreover
    from wf_e1 prec stack dfs1_pre_domain[OF pre] gray'
    have "\<forall>y \<in> set (stack e). \<exists>g \<in> gray e. y \<preceq> g in (stack e) \<and> reachable y g"
      unfolding wf_env_def by (metis insert_iff subsetCE precedes_mem(2))
    moreover
    from wf_e1 l scc have "sccs ?e' = {C . C \<subseteq> black ?e' \<and> is_scc C}"
      by (auto simp: wf_env_def dest: scc_partition)
    ultimately show ?thesis
      using l unfolding wf_env_def by simp
  qed

  from post l dist have sub: "subenv e ?e'"
    unfolding dfs_post_def subenv_def e1_def add_stack_incr_def
    by (auto simp: set_infty)

  from l have num: "\<infinity> \<le> num ?e' x"
    by (auto simp: set_infty)

  from l have "\<forall>y. xedge_to (stack ?e') (stack e) y \<longrightarrow> \<infinity> \<le> num ?e' y"
    unfolding xedge_to_def by auto

  with res wf_e' sub num show ?thesis
    unfolding dfs1_post_def res_def by simp
qed

text \<open>
  The following main lemma establishes the partial correctness
  of the two mutually recursive functions. The domain conditions
  appear explicitly as hypotheses, although we already know that
  they are subsumed by the preconditions. They are needed for the
  application of the ``partial induction'' rule generated by
  Isabelle for recursive functions whose termination was not proved.
  We will remove them in the next step.
\<close>

lemma dfs_partial_correct:
  fixes x roots e
  shows
  "\<lbrakk>dfs1_dfs_dom (Inl(x,e)); dfs1_pre x e\<rbrakk> \<Longrightarrow> dfs1_post x e (dfs1 x e)"
  "\<lbrakk>dfs1_dfs_dom (Inr(roots,e)); dfs_pre roots e\<rbrakk> \<Longrightarrow> dfs_post roots e (dfs roots e)"
proof (induct rule: dfs1_dfs.pinduct)
  fix x e
  let ?res1 = "dfs1 x e"
  let ?res' = "dfs (successors x) (add_stack_incr x e)"
  assume ind: "dfs_pre (successors x) (add_stack_incr x e)
           \<Longrightarrow> dfs_post (successors x) (add_stack_incr x e) ?res'"
     and pre: "dfs1_pre x e"
  have post: "dfs_post (successors x) (add_stack_incr x e) ?res'"
    by (rule ind) (rule dfs1_pre_dfs_pre[OF pre])
  show "dfs1_post x e ?res1"
  proof (cases "fst ?res' < int (sn e)")
    case True with pre post show ?thesis by (rule dfs_post_dfs1_post_case1)
  next
    case False
    with pre post show ?thesis by (rule dfs_post_dfs1_post_case2)
  qed
next
  fix roots e
  let ?res' = "dfs roots e"
  let ?dfs1 = "\<lambda>x. dfs1 x e"
  let ?dfs = "\<lambda>x e'. dfs (roots - {x}) e'"
  assume ind1: "\<And>x. \<lbrakk> roots \<noteq> {}; x = (SOME x. x \<in> roots);
                          \<not> num e x \<noteq> - 1; dfs1_pre x e \<rbrakk>
                \<Longrightarrow> dfs1_post x e (?dfs1 x)"
     and ind': "\<And>x res1.
                  \<lbrakk> roots \<noteq> {}; x = (SOME x. x \<in> roots);
                    res1 = (if num e x \<noteq> - 1 then (num e x, e) else ?dfs1 x);
                    dfs_pre (roots - {x}) (snd res1) \<rbrakk>
               \<Longrightarrow> dfs_post (roots - {x}) (snd res1) (?dfs x (snd res1))"
     and pre: "dfs_pre roots e"
  from pre have dom: "dfs1_dfs_dom (Inr (roots, e))"
    by (rule dfs_pre_dfs_dom)
  show "dfs_post roots e ?res'"
  proof (cases "roots = {}")
    case True
    with pre dom show ?thesis
      unfolding dfs_pre_def dfs_post_def subenv_def xedge_to_def
      by (auto simp: dfs.psimps)
  next
    case nempty: False
    define x where "x = (SOME x. x \<in> roots)"
    with nempty have x: "x \<in> roots" by (auto intro: someI)
    define res1 where
      "res1 = (if num e x \<noteq> - 1 then (num e x, e) else ?dfs1 x)"
    define res2 where
      "res2 = ?dfs x (snd res1)"
    have post1: "num e x = -1 \<longrightarrow> dfs1_post x e (?dfs1 x)"
    proof
      assume num: "num e x = -1"
      with pre x have "dfs1_pre x e"
        by (rule dfs_pre_dfs1_pre)
      with nempty num x_def show "dfs1_post x e (?dfs1 x)"
        by (simp add: ind1)
    qed
    have sub1: "subenv e (snd res1)"
    proof (cases "num e x = -1")
      case True
      with post1 res1_def show ?thesis
        by (auto simp: dfs1_post_def)
    next
      case False
      with res1_def show ?thesis by simp
    qed
    have wf1: "wf_env (snd res1)"
    proof (cases "num e x = -1")
      case True
      with res1_def post1 show ?thesis
        by (auto simp: dfs1_post_def)
    next
      case False
      with res1_def pre show ?thesis
        by (auto simp: dfs_pre_def)
    qed
    from post1 pre res1_def
    have res1: "dfs_pre (roots - {x}) (snd res1)"
      unfolding dfs_pre_def dfs1_post_def subenv_def by auto
    with nempty x_def res1_def ind'
    have post: "dfs_post (roots - {x}) (snd res1) (?dfs x (snd res1))"
      by blast
    with res2_def have sub2: "subenv (snd res1) (snd res2)"
      by (auto simp: dfs_post_def)
    from post res2_def have wf2: "wf_env (snd res2)"
      by (auto simp: dfs_post_def)
    from dom nempty x_def res1_def res2_def
    have res: "dfs roots e = (min (fst res1) (fst res2), snd res2)"
      by (auto simp add: dfs.psimps)
    show ?thesis
    proof -
      let ?n2 = "min (fst res1) (fst res2)"
      let ?e2 = "snd res2"

      from post res2_def 
      have "wf_env ?e2"
        unfolding dfs_post_def by auto

      moreover
      from sub1 sub2 have sub: "subenv e ?e2"
        by (rule subenv_trans)

      moreover
      have "x \<in> colored ?e2"
      proof (cases "num e x = -1")
        case True
        with post1 res1_def sub2 show ?thesis
          by (auto simp: dfs1_post_def subenv_def colored_def)
      next
        case False
        with pre sub show ?thesis
          by (auto simp: dfs_pre_def wf_env_def wf_num_def subenv_def colored_def)
      qed
      with post res2_def have "roots \<subseteq> colored ?e2"
        unfolding dfs_post_def by auto

      moreover
      have "\<forall>y \<in> roots. ?n2 \<le> num ?e2 y"
      proof
        fix y
        assume y: "y \<in> roots"
        show "?n2 \<le> num ?e2 y"
        proof (cases "y = x")
          case True
          show ?thesis
          proof (cases "num e x = -1")
            case True
            with post1 res1_def have "fst res1 \<le> num (snd res1) x"
              unfolding dfs1_post_def by auto
            moreover
            from wf1 wf2 sub2 have "num (snd res1) x \<le> num (snd res2) x"
              unfolding wf_env_def by (auto elim: subenv_num)
            ultimately show ?thesis
              using \<open>y=x\<close> by simp
          next
            case False
            with res1_def wf1 wf2 sub2 have "fst res1 \<le> num (snd res2) x"
              unfolding wf_env_def by (auto elim: subenv_num)
            with \<open>y=x\<close> show ?thesis by simp
          qed
        next
          case False
          with y post res2_def have "fst res2 \<le> num ?e2 y"
            unfolding dfs_post_def by auto
          thus ?thesis by simp
        qed
      qed

      moreover
      {
        assume n2: "?n2 \<noteq> \<infinity>"
        hence "(fst res1 \<noteq> \<infinity> \<and> ?n2 = fst res1)
             \<or> (fst res2 \<noteq> \<infinity> \<and> ?n2 = fst res2)" by auto
        hence "\<exists>r \<in> roots. \<exists>y \<in> set (stack ?e2). num ?e2 y = ?n2 \<and> reachable r y"
        proof
          assume n2: "fst res1 \<noteq> \<infinity> \<and> ?n2 = fst res1"
          have "\<exists>y \<in> set (stack (snd res1)). 
                     num (snd res1) y = (fst res1) \<and> reachable x y"
          proof (cases "num e x = -1")
            case True
            with post1 res1_def n2 show ?thesis
              unfolding dfs1_post_def by auto
          next
            case False
            with wf1 res1_def n2 have "x \<in> set (stack (snd res1))"
              unfolding wf_env_def wf_color_def wf_num_def colored_def by auto
            with False res1_def show ?thesis
              by auto
          qed
          with sub2 x n2 show ?thesis
            unfolding subenv_def by fastforce
        next
          assume "fst res2 \<noteq> \<infinity> \<and> ?n2 = fst res2"
          with post res2_def show ?thesis
            unfolding dfs_post_def by auto
        qed
      }
      hence "?n2 = \<infinity> \<or> (\<exists>r \<in> roots. \<exists>y \<in> set (stack ?e2). num ?e2 y = ?n2 \<and> reachable r y)"
        by blast

      moreover
      have "\<forall>y. xedge_to (stack ?e2) (stack e) y \<longrightarrow> ?n2 \<le> num ?e2 y"
      proof (clarify)
        fix y
        assume y: "xedge_to (stack ?e2) (stack e) y"
        show "?n2 \<le> num ?e2 y"
        proof (cases "num e x = -1")
          case True
          from sub1 obtain s1 where
            s1: "stack (snd res1) = s1 @ stack e"
            by (auto simp: subenv_def)
          from sub2 obtain s2 where
            s2: "stack ?e2 = s2 @ stack (snd res1)"
            by (auto simp: subenv_def)
          from y obtain zs z where
            z: "stack ?e2 = zs @ stack e" "z \<in> set zs" 
               "y \<in> set (stack e)" "edge z y"
            by (auto simp: xedge_to_def)
          with s1 s2 have "z \<in> (set s1) \<union> (set s2)" by auto
          thus ?thesis
          proof
            assume "z \<in> set s1"
            with s1 z have "xedge_to (stack (snd res1)) (stack e) y"
              by (auto simp: xedge_to_def)
            with post1 res1_def \<open>num e x = -1\<close>
            have "fst res1 \<le> num (snd res1) y"
              by (auto simp: dfs1_post_def)
            moreover
            with wf1 wf2 sub2 have "num (snd res1) y \<le> num ?e2 y"
              unfolding wf_env_def by (auto elim: subenv_num)
            ultimately show ?thesis by simp
          next
            assume "z \<in> set s2"
            with s1 s2 z have "xedge_to (stack ?e2) (stack (snd res1)) y"
              by (auto simp: xedge_to_def)
            with post res2_def show ?thesis
              by (auto simp: dfs_post_def)
          qed
        next
          case False
          with y post res1_def res2_def show ?thesis
            unfolding dfs_post_def by auto
        qed
      qed

      ultimately show ?thesis
        using res unfolding dfs_post_def by simp
    qed
  qed
qed

section \<open>Theorems establishing total correctness\<close>

text \<open>
  Combining the previous theorems, we show total correctness for
  both the auxiliary functions and the main function @{text tarjan}.
\<close>

theorem dfs_correct:
  "dfs1_pre x e \<Longrightarrow> dfs1_post x e (dfs1 x e)"
  "dfs_pre roots e \<Longrightarrow> dfs_post roots e (dfs roots e)"
  using dfs_partial_correct dfs1_pre_dfs1_dom dfs_pre_dfs_dom by (blast+)

theorem tarjan_correct: "tarjan = { C . is_scc C \<and> C \<subseteq> vertices }"
proof -
  have "dfs_pre vertices init_env"
    by (auto simp: dfs_pre_def init_env_def wf_env_def wf_color_def colored_def
                   wf_num_def no_black_to_white_def is_scc_def precedes_def)
  hence res: "dfs_post vertices init_env (dfs vertices init_env)"
    by (rule dfs_correct)
  thus ?thesis
    by (auto simp: tarjan_def init_env_def dfs_post_def wf_env_def wf_color_def 
                   colored_def subenv_def)
qed

end \<comment> \<open>context graph\<close>
end \<comment> \<open>theory Tarjan\<close>
