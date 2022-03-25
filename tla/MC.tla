---- MODULE MC ----
EXTENDS SCC, TLC

\* CONSTANT definitions @modelParameterConstants:0root
const_164819784452216000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:1Node
const_164819784452217000 == 
{1,2,3,4,5,6}
----

\* CONSTANT definitions @modelParameterConstants:2Succs
const_164819784452218000 == 
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
\* Created Fri Mar 25 09:44:04 CET 2022 by vincent
