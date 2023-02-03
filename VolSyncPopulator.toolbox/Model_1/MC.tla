---- MODULE MC ----
EXTENDS VolSyncPopulator, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B, C, D, E, F
----

\* MV CONSTANT definitions OIDs
const_1675442563596115000 == 
{A, B, C, D, E, F}
----

\* SYMMETRY definition
symm_1675442563596116000 == 
Permutations(const_1675442563596115000)
----

\* PROPERTY definition @modelCorrectnessProperties:1
prop_1675442563597119000 ==
<>(Cardinality(Objs)=2)
----
=============================================================================
\* Modification History
\* Created Fri Feb 03 11:42:43 EST 2023 by jstrunk
