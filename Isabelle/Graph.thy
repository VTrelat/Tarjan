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

function unite :: "'v \<Rightarrow> 'v \<Rightarrow> 'v env" where
  "unite v w e =
      (if (S e v = S e w) then e
      else let r = hd(stack e) and r' = hd(tl(stack e)) and  e' = e \<lparr> stack := tl(stack e) and s:=s e (r <- s e r \<union> s e r', r' <- s e r \<union> s e r') \<rparr>
          in unite v w e')"

function dfs :: "'v \<Rightarrow> 'v env \<Rightarrow> 'v env" and dfss :: "'v \<Rightarrow> 'v set \<Rightarrow> 'v env \<Rightarrow> 'v env" where
  "dfs v e =
  (let e1 = e1\<lparr>visited := visited e \<union> {v},
              stack := (v :: stack e)\<rparr> in let
      e' = dfss (succ v) e1
  in if v = hd(stack e')
      then e'\<lparr>sccs:=sccs e' \<union> (S e v),
              explored:=explored e' \<union> (S e u),
              stack:=tl(stack e')\<rparr>
    else e')"
| "dfss v vs e =
   (if vs={} then e
   else let w = SOME x. x \<in> vs
     in if w \<in> explored e
        then dfss v (vs\<setminus>{w}) e
      else if w \<notin> visited e
        then dfs w e
      else unite v w e)"
  by pat_comleteness auto

end
end