-------------------------- MODULE VolSyncPopulator --------------------------
(***************************************************************************)
(* Model for the "data populator" functionality in VolSync.                *)
(*                                                                         *)
(* The goal with this model is to verify that the populator controller can *)
(* properly interact with the ReplicationDestination controller to         *)
(* provision PVCs based on the LatestImage that has been saved.            *)
(***************************************************************************)
EXTENDS FiniteSets, TLC
CONSTANTS OIDs,  \* A symmetry set representing object UUIDs
          nil

(***************************************************************************)
(* The allowable values for an object's kind                               *)
(***************************************************************************)
ObjKinds == {"RD", "VS", "PV", "PVC"}


(*
--fair algorithm populator
variables
    Objs = {}  \* The set of objects in the system

define
    TypeOk == /\ \A o \in Objs: /\ \A f \in {    \* Objects must have at least:
                                        "k",     \* * kind
                                        "oid"    \* * UUID
                                   }: f \in DOMAIN o
                                /\ o.k \in ObjKinds         \* All objects have a valid kind
                                /\ o.oid \in OIDs           \* All objects have a valid ID
                                /\ \A x \in Objs: \/ x = o  \* IDs are unique
                                                  \/ x.oid # o.oid

    \* FreeOIDs is the current set of unused IDs
    FreeOIDs == OIDs \ {o.oid : o \in Objs}
    \* Empty record
    empty == [x \in {} |-> {}]
end define

process User \in {"user"}
begin
UStart:
    with i \in FreeOIDs do
        Objs := Objs \cup { [oid |-> i, k |-> "RD", LI |-> nil] };
    end with;
end process

process RDController \in {"RDC"}
begin
RDBegin:
    with rd \in {o \in Objs: o.k = "RD"}, i \in FreeOIDs do
        Objs := (Objs \ {rd}) \cup { [oid |-> i, k |-> "VS"], [rd EXCEPT !.LI = i] };
    end with;
    print(Objs);
end process
end algorithm
*)



\* BEGIN TRANSLATION (chksum(pcal) = "60ba6cfc" /\ chksum(tla) = "582f3ad5")
VARIABLES Objs, pc

(* define statement *)
TypeOk == /\ \A o \in Objs: /\ \A f \in {
                                    "k",
                                    "oid"
                               }: f \in DOMAIN o
                            /\ o.k \in ObjKinds
                            /\ o.oid \in OIDs
                            /\ \A x \in Objs: \/ x = o
                                              \/ x.oid # o.oid


FreeOIDs == OIDs \ {o.oid : o \in Objs}

empty == [x \in {} |-> {}]


vars == << Objs, pc >>

ProcSet == ({"user"}) \cup ({"RDC"})

Init == (* Global variables *)
        /\ Objs = {}
        /\ pc = [self \in ProcSet |-> CASE self \in {"user"} -> "UStart"
                                        [] self \in {"RDC"} -> "RDBegin"]

UStart(self) == /\ pc[self] = "UStart"
                /\ \E i \in FreeOIDs:
                     Objs' = (Objs \cup { [oid |-> i, k |-> "RD", LI |-> nil] })
                /\ pc' = [pc EXCEPT ![self] = "Done"]

User(self) == UStart(self)

RDBegin(self) == /\ pc[self] = "RDBegin"
                 /\ \E rd \in {o \in Objs: o.k = "RD"}:
                      \E i \in FreeOIDs:
                        Objs' = ((Objs \ {rd}) \cup { [oid |-> i, k |-> "VS"], [rd EXCEPT !.LI = i] })
                 /\ PrintT((Objs'))
                 /\ pc' = [pc EXCEPT ![self] = "Done"]

RDController(self) == RDBegin(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {"user"}: User(self))
           \/ (\E self \in {"RDC"}: RDController(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
-----------------------------------------------------------------------------


=============================================================================
\* Modification History
\* Last modified Fri Feb 03 11:42:33 EST 2023 by jstrunk
\* Created Fri Feb 03 09:54:49 EST 2023 by jstrunk
