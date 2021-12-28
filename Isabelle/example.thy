theory example
  imports Main

begin

declare [[names_short]]
datatype 'a list = Empty | Cons 'a "'a list"

fun length :: "'a list \<Rightarrow> nat"
  where
  "length Empty = 0"
| "length (Cons x xs) = 1 + length xs"

(* Found termination order: "size <*mlex*> {}" *)

fun concat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
  "concat Empty xs = xs"
| "concat (Cons x xs) ys =  Cons x (concat xs ys)"

(* Found termination order: "(\<lambda>p. size (fst p)) <*mlex*> {}" *)

fun add_tl :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
  "add_tl x Empty = Cons x Empty"
| "add_tl x (Cons y ys) = Cons y (add_tl x ys)"

(* Found termination order: "(\<lambda>p. size (snd p)) <*mlex*> {}" *)

fun reverse :: "'a list \<Rightarrow> 'a list"
  where
  "reverse Empty = Empty"
| "reverse (Cons x xs) = concat (reverse xs) (Cons x Empty)"

(* Found termination order: "size <*mlex*> {}" *)

lemma concat_empty [simp]: "concat xs Empty = xs"
  apply(induction xs)
  apply(auto)
  done

lemma concat_assoc [simp]: "concat (concat xs ys) zs = concat xs (concat ys zs)"
  apply(induction xs)
   apply(auto)
  done

lemma reverse_concat [simp]: "reverse (concat xs ys) = concat (reverse ys) (reverse xs)"
  apply(induction xs)
(*  1. reverse (concat Empty ys) = concat (reverse ys) (reverse Empty)
    2. \<And>x1 xs.
          reverse (concat xs ys) = concat (reverse ys) (reverse xs) \<Longrightarrow>
          reverse (concat (Cons x1 xs) ys) = concat (reverse ys) (reverse (Cons x1 xs)) *)
(* after reverse_empty :
 1. \<And>x1 xs.
       reverse (concat xs ys) = concat (reverse ys) (reverse xs) \<Longrightarrow>
       concat (concat (reverse ys) (reverse xs)) (Cons x1 Empty) =
       concat (reverse ys) (concat (reverse xs) (Cons x1 Empty))
*)
  apply(auto)
  done
(*
 1. reverse ys = concat (reverse ys) Empty
 2. \<And>x1 xs.
       reverse (concat xs ys) = concat (reverse ys) (reverse xs) \<Longrightarrow>
       concat (concat (reverse ys) (reverse xs)) (Cons x1 Empty) =
       concat (reverse ys) (concat (reverse xs) (Cons x1 Empty))
*)

theorem reverse_reverse [simp]: "reverse(reverse(x)) = x"
  apply(induction x)
  apply(auto)
  done

 (* 1. \<And>x1 x. reverse (reverse x) = x \<Longrightarrow> reverse (concat (reverse x) (Cons x1 Empty)) = Cons x1 x *)
 (* assoc *)
end