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

BoundedSeq(S, n) ==
  \* non-empty sequences of length at most n of elements in S
  UNION {[1..m -> S] : m \in 1 .. n}

SimplePath(n) ==
  \* path in the graph without repetitions of length at most n
  {p \in BoundedSeq(Node, n) : 
     /\ \A i \in 1 .. Len(p)-1 : p[i+1] \in Succs[p[i]]
     /\ \A i,j \in 1 .. Len(p) : p[i] = p[j] => i = j}

ReachableByPath(m,n) ==
  \* node n is reachable from node m
  \E p \in SimplePath(Cardinality(Node)) : p[1] = m /\ p[Len(p)] = n

Connected ==
  \* pre-compute the reachability relation (and let TLC cache it)
  LET C[N \in SUBSET Node] ==
      \* C[N] is a Boolean matrix that represents nodes connected by paths
      \* whose interior nodes (i.e., those except the start and end node) 
      \* are all in set N
      IF N = {} THEN [x,y \in Node |-> x = y \/ y \in Succs[x]]
      ELSE LET u == CHOOSE n \in N : TRUE
               Cu == C[N \ {u}]
           IN  [x,y \in Node |-> \/ Cu[x,y]
                                 \/ Cu[x,u] /\ Cu[u,y]]
  IN  C[Node]
  
Reachable(m,n) == Connected[m,n]

(*--algorithm SCC {
    variables 
      explored = {},
      visited = {},
      dfstack = << >>,
      sccs = {},
      uf = [n \in Node |-> {n}];

    macro unite(v,w) {
      \* merge the UF sets associated with v and w
      with (merged = uf[v] \union uf[w]) {
        uf := [n \in Node |-> IF n \in merged THEN merged ELSE uf[n]];
      }
    }

    procedure dfs(v) 
      variables todo, w;
    {
l0:   visited := visited \union {v};
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
l3:        while (uf[v] # uf[w]) {
              unite(dfstack[1], dfstack[2]);
              dfstack := Tail(dfstack);
           }
        }
      }; \* end while (todo # {})
l4:   if (v = Head(dfstack)) {
         sccs := sccs \union {uf[v]};
         explored := explored \union uf[v];
         dfstack := Tail(dfstack);
      };
      return;
    } \* end dfs
    
    { \* main algorithm
main: call dfs(root);
    }
    
}*)
\* BEGIN TRANSLATION (chksum(pcal) = "d3d06bc9" /\ chksum(tla) = "d521168b")
CONSTANT defaultInitValue
VARIABLES explored, visited, dfstack, sccs, uf, pc, stack, v, todo, w

vars == << explored, visited, dfstack, sccs, uf, pc, stack, v, todo, w >>

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
        /\ stack = << >>
        /\ pc = "main"

l0 == /\ pc = "l0"
      /\ visited' = (visited \union {v})
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
      /\ UNCHANGED << explored, visited, dfstack, sccs, uf, stack, v >>

l2 == /\ pc = "l2"
      /\ /\ stack' = << [ procedure |->  "dfs",
                          pc        |->  "l1",
                          todo      |->  todo,
                          w         |->  w,
                          v         |->  v ] >>
                      \o stack
         /\ v' = w
      /\ todo' = defaultInitValue
      /\ w' = defaultInitValue
      /\ pc' = "l0"
      /\ UNCHANGED << explored, visited, dfstack, sccs, uf >>

l3 == /\ pc = "l3"
      /\ IF uf[v] # uf[w]
            THEN /\ LET merged == uf[(dfstack[1])] \union uf[(dfstack[2])] IN
                      uf' = [n \in Node |-> IF n \in merged THEN merged ELSE uf[n]]
                 /\ dfstack' = Tail(dfstack)
                 /\ pc' = "l3"
            ELSE /\ pc' = "l1"
                 /\ UNCHANGED << dfstack, uf >>
      /\ UNCHANGED << explored, visited, sccs, stack, v, todo, w >>

l4 == /\ pc = "l4"
      /\ IF v = Head(dfstack)
            THEN /\ sccs' = (sccs \union {uf[v]})
                 /\ explored' = (explored \union uf[v])
                 /\ dfstack' = Tail(dfstack)
            ELSE /\ TRUE
                 /\ UNCHANGED << explored, dfstack, sccs >>
      /\ pc' = Head(stack).pc
      /\ todo' = Head(stack).todo
      /\ w' = Head(stack).w
      /\ v' = Head(stack).v
      /\ stack' = Tail(stack)
      /\ UNCHANGED << visited, uf >>

dfs == l0 \/ l1 \/ l2 \/ l3 \/ l4

main == /\ pc = "main"
        /\ /\ stack' = << [ procedure |->  "dfs",
                            pc        |->  "Done",
                            todo      |->  todo,
                            w         |->  w,
                            v         |->  v ] >>
                        \o stack
           /\ v' = root
        /\ todo' = defaultInitValue
        /\ w' = defaultInitValue
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
  /\ \A i,j \in 1 .. Len(dfstack) : i < j => Reachable(dfstack[j], dfstack[i])
  /\ pc = "l0" => \/ dfstack = << >>
                  \/ Reachable(dfstack[1], v) 
  /\ pc \in {"l1", "l2", "l3"} => \A n \in Range(dfstack) : Reachable(n,v)

=============================================================================
\* Modification History
\* Last modified Fri Apr 01 15:52:04 CEST 2022 by merz
\* Created Fri Mar 04 08:28:16 CET 2022 by merz
