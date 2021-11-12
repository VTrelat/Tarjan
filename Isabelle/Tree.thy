theory Tree
imports Main

begin
datatype 'a tree = Nil | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Nil = Nil" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma mirror_mirror [simp]: "mirror (mirror t) = t"
  apply(induction t)
  apply(auto)
  done

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Nil = []" |
"contents (Node l a r) = (contents l)@[a]@(contents r)"

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order Nil = []" |
"pre_order (Node l x r) = [x]@(pre_order l)@(pre_order r)"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order Nil = []" |
"post_order (Node l x r) = (post_order l)@(post_order r)@[x]"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev [] = []" |
"rev (x#xs) = (rev xs)@[x]"

lemma cons_rev [simp]: "x#rev xs = rev (xs@[x])"
  apply(induction xs)
   apply(auto)
  done

lemma rev_app [simp]: "rev(l1)@rev(l2) = rev(l2@l1)"
  apply(induct l1, auto)
  apply(induct l2, auto)
  done

theorem pre_post : "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
  done

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = []" |
"intersperse a [x] = [x]" |
"intersperse a (x#y#xs) = [x]@[a]@[y]@xs"

fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"map f [] = []" |
"map f (x#xs) = (f x)#(map f xs)"

theorem map_intersperse : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule:intersperse.induct)
  apply(auto)
  done

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev  [] ys = ys" |
"itrev (x#xs) ys = itrev xs (x#ys)"

lemma "itrev xs ys = rev xs @ ys"
  apply(induction xs arbitrary: ys)
  apply(auto)
  done

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"


end