---- MODULE MC ----
EXTENDS VolSyncPopulator, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
A, B, C, D, E, F
----

\* MV CONSTANT definitions OIDs
const_1675460136693148000 == 
{A, B, C, D, E, F}
----

\* SYMMETRY definition
symm_1675460136693149000 == 
Permutations(const_1675460136693148000)
----

=============================================================================
\* Modification History
\* Created Fri Feb 03 16:35:36 EST 2023 by jstrunk
