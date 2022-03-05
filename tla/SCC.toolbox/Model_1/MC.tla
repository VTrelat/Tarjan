---- MODULE MC ----
EXTENDS SCC, TLC

\* CONSTANT definitions @modelParameterConstants:0root
const_1646468547630105000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:1Node
const_1646468547630106000 == 
{1,2,3,4,5,6}
----

\* CONSTANT definitions @modelParameterConstants:2Succs
const_1646468547630107000 == 
<< 
{2},
{3},
{2,4},
{2,3,5},
{6},
{5}
>>
----

\* Constant expression definition @modelExpressionEval
const_expr_1646468547630108000 == 
Connected
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_1646468547630108000>>)
----

=============================================================================
\* Modification History
\* Created Sat Mar 05 09:22:27 CET 2022 by merz
