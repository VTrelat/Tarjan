-------------------------------- MODULE SCC --------------------------------
(***************************************************************************)
(* Sequential algorithm for computing SCCs from Vincent Bloemen's PhD      *)
(* thesis "Strong Connectivity and Shortest Paths for Checking Models"     *)
(* (Univ. Twente, 2019).                                                   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Node, Succs, root
ASSUME /\ IsFiniteSet(Node)
       /\ Succs \in [Node -> SUBSET Node]
       /\ root \in Node

Reachable ==
  \* Compute a Boolean matrix that indicates, for each pair of nodes,
  \* if there exists a path that links the two nodes. The result can
  \* be cached by TLC, avoiding recomputation.
  LET R[N \in SUBSET Node] ==
      \* Matrix representing the existence of paths whose inner nodes
      \* (i.e., except for the source and the target) are all in the
      \* set of nodes N.
      IF N = {}
      THEN [m,n \in Node |-> m = n \/ n \in Succs[m]]
      ELSE LET u == CHOOSE u \in N : TRUE
               Ru == R[N \ {u}]
           IN  [m,n \in Node |-> \/ Ru[m,n]
                                 \/ Ru[m,u] /\ Ru[u,n]]
  IN  R[Node]


(*--algorithm SCC {
    variables
      explored = {},
      visited = {},
      dfstack = << >>,
      sccs = {},
      uf = [n \in Node |-> {n}];

(*
    macro unite(v,w) {
      \* merge the UF sets associated with v and w
      with (merged = uf[v] \union uf[w]) {
        uf := [n \in Node |-> IF n \in merged THEN merged ELSE uf[n]];
      }
    }
*)
    macro mergeto(w) {
      with (iw = CHOOSE i \in 1 .. Len(dfstack) : w \in uf[dfstack[i]],
            cc = UNION {uf[dfstack[i]] : i \in 1 .. iw}) {
        uf := [n \in Node |-> IF n \in cc THEN cc ELSE uf[n]];
        dfstack := SubSeq(dfstack, iw, Len(dfstack));
      }
    }

    procedure dfs(v)
      variables todo, w, oldstack, olduf;
    {
l0:   visited := visited \union {v};
      oldstack := dfstack; olduf := uf;
      dfstack := << v >> \o dfstack;
      todo := Succs[v];
l1:   while (todo # {}) {
        with (n \in todo) { w := n; todo := todo \ {n} };
        if (w \in explored) {
           skip;
        }
        else if (w \notin visited) {
l2:        call dfs(w);
        }
        else {
(*
l3:        while (uf[v] # uf[w]) {
              unite(dfstack[1], dfstack[2]);
              dfstack := Tail(dfstack);
           }
*)
l3:        mergeto(w)
        }
      }; \* end while (todo # {})
l4:   if (v = Head(dfstack)) {
         sccs := sccs \union {uf[v]};
         explored := explored \union uf[v];
         dfstack := Tail(dfstack);
      };
l5:   return;
    } \* end dfs

    { \* main algorithm
main: call dfs(root);
    }

}*)
\* BEGIN TRANSLATION (chksum(pcal) = "b6ff2417" /\ chksum(tla) = "754ae873")
CONSTANT defaultInitValue
VARIABLES explored, visited, dfstack, sccs, uf, pc, stack, v, todo, w, 
          oldstack, olduf

vars == << explored, visited, dfstack, sccs, uf, pc, stack, v, todo, w, 
           oldstack, olduf >>

Init == (* Global variables *)
        /\ explored = {}
        /\ visited = {}
        /\ dfstack = << >>
        /\ sccs = {}
        /\ uf = [n \in Node |-> {n}]
        (* Procedure dfs *)
        /\ v = defaultInitValue
        /\ todo = defaultInitValue
        /\ w = defaultInitValue
        /\ oldstack = defaultInitValue
        /\ olduf = defaultInitValue
        /\ stack = << >>
        /\ pc = "main"

l0 == /\ pc = "l0"
      /\ visited' = (visited \union {v})
      /\ oldstack' = dfstack
      /\ olduf' = uf
      /\ dfstack' = << v >> \o dfstack
      /\ todo' = Succs[v]
      /\ pc' = "l1"
      /\ UNCHANGED << explored, sccs, uf, stack, v, w >>

l1 == /\ pc = "l1"
      /\ IF todo # {}
            THEN /\ \E n \in todo:
                      /\ w' = n
                      /\ todo' = todo \ {n}
                 /\ IF w' \in explored
                       THEN /\ TRUE
                            /\ pc' = "l1"
                       ELSE /\ IF w' \notin visited
                                  THEN /\ pc' = "l2"
                                  ELSE /\ pc' = "l3"
            ELSE /\ pc' = "l4"
                 /\ UNCHANGED << todo, w >>
      /\ UNCHANGED << explored, visited, dfstack, sccs, uf, stack, v, oldstack, 
                      olduf >>

l2 == /\ pc = "l2"
      /\ /\ stack' = << [ procedure |->  "dfs",
                          pc        |->  "l1",
                          todo      |->  todo,
                          w         |->  w,
                          oldstack  |->  oldstack,
                          olduf     |->  olduf,
                          v         |->  v ] >>
                      \o stack
         /\ v' = w
      /\ todo' = defaultInitValue
      /\ w' = defaultInitValue
      /\ oldstack' = defaultInitValue
      /\ olduf' = defaultInitValue
      /\ pc' = "l0"
      /\ UNCHANGED << explored, visited, dfstack, sccs, uf >>

l3 == /\ pc = "l3"
      /\ LET iw == CHOOSE i \in 1 .. Len(dfstack) : w \in uf[dfstack[i]] IN
           LET cc == UNION {uf[dfstack[i]] : i \in 1 .. iw} IN
             /\ uf' = [n \in Node |-> IF n \in cc THEN cc ELSE uf[n]]
             /\ dfstack' = SubSeq(dfstack, iw, Len(dfstack))
      /\ pc' = "l1"
      /\ UNCHANGED << explored, visited, sccs, stack, v, todo, w, oldstack, 
                      olduf >>

l4 == /\ pc = "l4"
      /\ IF v = Head(dfstack)
            THEN /\ sccs' = (sccs \union {uf[v]})
                 /\ explored' = (explored \union uf[v])
                 /\ dfstack' = Tail(dfstack)
            ELSE /\ TRUE
                 /\ UNCHANGED << explored, dfstack, sccs >>
      /\ pc' = "l5"
      /\ UNCHANGED << visited, uf, stack, v, todo, w, oldstack, olduf >>

l5 == /\ pc = "l5"
      /\ pc' = Head(stack).pc
      /\ todo' = Head(stack).todo
      /\ w' = Head(stack).w
      /\ oldstack' = Head(stack).oldstack
      /\ olduf' = Head(stack).olduf
      /\ v' = Head(stack).v
      /\ stack' = Tail(stack)
      /\ UNCHANGED << explored, visited, dfstack, sccs, uf >>

dfs == l0 \/ l1 \/ l2 \/ l3 \/ l4 \/ l5

main == /\ pc = "main"
        /\ /\ stack' = << [ procedure |->  "dfs",
                            pc        |->  "Done",
                            todo      |->  todo,
                            w         |->  w,
                            oldstack  |->  oldstack,
                            olduf     |->  olduf,
                            v         |->  v ] >>
                        \o stack
           /\ v' = root
        /\ todo' = defaultInitValue
        /\ w' = defaultInitValue
        /\ oldstack' = defaultInitValue
        /\ olduf' = defaultInitValue
        /\ pc' = "l0"
        /\ UNCHANGED << explored, visited, dfstack, sccs, uf >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == dfs \/ main
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

StackFrame ==
  [procedure : {"dfs"},
   pc : {"l1", "Done"},
   todo : (SUBSET Node) \union {defaultInitValue},
   w : Node \union {defaultInitValue},
   v : Node \union {defaultInitValue}]

TypeOK ==
  /\ explored \in SUBSET Node
  /\ visited \in SUBSET Node
  /\ dfstack \in Seq(Node)
  /\ sccs \in SUBSET (SUBSET Node)
  /\ uf \in [Node -> SUBSET Node]
  /\ v \in Node \union {defaultInitValue}
  /\ todo \in (SUBSET Node) \union {defaultInitValue}
  /\ w \in Node \union {defaultInitValue}
  /\ stack \in Seq(StackFrame)
  /\ pc \in {"main", "l0", "l1", "l2", "l3", "l4", "Done"}

Range(f) == {f[x] : x \in DOMAIN f}

Inv ==
  /\ explored \subseteq visited
  /\ Range(dfstack) \subseteq visited
  /\ explored \cap Range(dfstack) = {}
  /\ \A i,j \in 1 .. Len(dfstack) : dfstack[i] = dfstack[j] => i = j
  /\ \A m,n \in Node : m \in uf[n] => uf[m] = uf[n]
  /\ \A m,n \in Range(dfstack) : m # n => uf[m] \cap uf[n] = {}
  /\ \A n \in Node : n \notin visited => uf[n] = {n}
  /\ UNION {uf[n] : n \in Range(dfstack)} = visited \ explored
  /\ \A i,j \in 1 .. Len(dfstack) : i <= j => Reachable[dfstack[j], dfstack[i]]
  /\ pc \in {"l0", "l1", "l2", "l3", "l4"} => \A n \in Range(dfstack) : Reachable[n,v]
(*
  /\ pc \in {"l1", "l2", "l3", "l4", "l5"} => 
        \A n \in Range(dfstack) : Reachable[v,n] =>
             \/ v \in uf[n]
             \/ \E m \in todo : Reachable[m,n]
             \/ pc \in {"l2","l3"} /\ Reachable[w,n]
*)
  /\ pc \in {"l1", "l4"} =>
        \A n \in Range(dfstack) : \A m \in Succs[v] \ todo :
             Reachable[m,n] => m \in uf[v]
  /\ pc \in {"l1", "l4"} => \A m \in Succs[v] \ todo : m \in explored \union uf[Head(dfstack)]
  /\ pc \in {"l1", "l2", "l3", "l4"} =>
        \A n \in Range(Tail(dfstack)) : uf[n] = olduf[n]
  /\ \A x \in explored : \A y \in Node : Reachable[x,y] => y \in explored
  /\ pc = "l5" => \/ v \in explored /\ dfstack = oldstack
                  \/ v \in uf[Head(dfstack)] /\ \A n \in Range(Tail(dfstack)) : uf[n] = olduf[n]
  /\ pc = "l5" => Range(dfstack) \subseteq Range(oldstack)
(*
  /\ pc = "l5" => \A i \in 1 .. Len(oldstack) : \A j \in 1 .. i : \A u \in olduf[oldstack[j]] :
                     Reachable[u,v] /\ Reachable[v, oldstack[i]] => uf[oldstack[i]] = uf[oldstack[j]]
*)
  /\ pc \in {"l1", "l4"} => v \in uf[Head(dfstack)]
  /\ pc = "l4" /\ v \in Range(dfstack) => \A m \in Range(oldstack) : ~ Reachable[v,m]
  /\ pc = "l4" => Range(dfstack) \subseteq Range(oldstack) \union {v}

=============================================================================
\* Modification History
\* Last modified Wed Jun 15 09:46:29 CEST 2022 by merz
\* Created Fri Mar 04 08:28:16 CET 2022 by merz
