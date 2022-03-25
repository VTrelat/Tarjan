---- MODULE MC ----
EXTENDS SCC, TLC

\* CONSTANT definitions @modelParameterConstants:0root
const_164819822356122000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:1Node
const_164819822356123000 == 
{1, 2, 3, 4, 5, 6}
----

\* CONSTANT definitions @modelParameterConstants:2Succs
const_164819822356124000 == 
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
\* Created Fri Mar 25 09:50:23 CET 2022 by vincent
