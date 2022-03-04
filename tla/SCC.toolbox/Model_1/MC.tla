---- MODULE MC ----
EXTENDS SCC, TLC

\* CONSTANT definitions @modelParameterConstants:0root
const_164638949300882000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:1Node
const_164638949300883000 == 
{1,2,3,4,5,6}
----

\* CONSTANT definitions @modelParameterConstants:2Succs
const_164638949300884000 == 
<< 
{2},
{3},
{2,4},
{2,3,5},
{6},
{5}
>>
----

=============================================================================
\* Modification History
\* Created Fri Mar 04 11:24:53 CET 2022 by merz
