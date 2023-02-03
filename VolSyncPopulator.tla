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
    TypeOk == /\ \A o \in Objs: /\ o.k \in ObjKinds         \* All objects have a valid kind
                                /\ o.oid \in OIDs           \* All objects have a valid ID
                                /\ o.deleted \in BOOLEAN    \* All objects have a deletion flag
              /\ \A x, y \in Objs: x = y \/ x.oid # y.oid    \* IDs are unique

    \* FreeOIDs is the current set of unused IDs
    FreeOIDs == OIDs \ {o.oid : o \in Objs}

    \* Empty record
    empty == [x \in {} |-> {}]
end define

(***************************************************************************)
(* The "user":                                                             *)
(*                                                                         *)
(* * Creates and deletes ReplicationDestination objects.                   *)
(*                                                                         *)
(* * Creates and deletes PVCs to be populated from an RD.                  *)
(***************************************************************************)
process User \in {"user"}
begin
UStart:
either  \* Create a new ReplicationDestination
    with i \in FreeOIDs do
        Objs := Objs \cup { [oid |-> i, k |-> "RD", deleted |-> FALSE, LI |-> nil] };
    end with;
or      \* Delete a ReplicationDestination
    with rd \in {o \in Objs: o.k = "RD" /\ o.deleted = FALSE} do
        Objs := (Objs \ {rd}) \cup {[rd EXCEPT !.deleted = TRUE]};
    end with;
(*
or      \* Create a PVC to be populated
    skip;  \* Not implemented
or      \* Deletee a PVC we created
    skip;  \* Not implemented
*)
end either;
goto UStart;
end process

(***************************************************************************)
(* The garbage collector frees deleted objects, cascading the deletes      *)
(* according to the owner references.                                      *)
(***************************************************************************)
process GarbageCollector \in {"GC"}
begin
GCStart:
either  \* Propagate deletion to owned objects 
    skip;  \* Not implemented
or      \* Remove deleted objects w/o dependents
    skip;  \* Not implemented
end either;
\* goto GCStart
end process

(***************************************************************************)
(* The RD controller periodically takes a new snapshot of the data and     *)
(* updates the "LatestImage" field w/ the name of the new VolumeSnapshot   *)
(* object.  It is also responsible for cleaning up old snapshots that are  *)
(* no longer referenced as the LatestImage.                                *)
(***************************************************************************)
process RDController \in {"RDC"}
begin
RDStart:
either  \* Create a new Snap (and update LatestImage)
    with rd \in {o \in Objs: o.k = "RD"},
         i \in FreeOIDs do
        Objs := (Objs \ {rd}) \cup { [oid |-> i, k |-> "VS", owner |-> rd.oid, deleted |-> FALSE], [rd EXCEPT !.LI = i] };
    end with;
or      \* Delete Snaps from an old LI
    with vs \in {o \in Objs: /\ o.k = "VS"
                             /\ o.deleted = FALSE
                                \* The VS is not refereced as an RD's LI.
                                \* ASSUMPTION: There are no other reasons to have a VS than as LI
                             /\ o.oid \notin { rd.LI: rd \in {x \in Objs: x.k = "RD"} } } do
        Objs := (Objs \ {vs}) \cup {[vs EXCEPT !.deleted = TRUE]};
    end with;
end either;
goto RDStart;
end process
end algorithm
*)



\* BEGIN TRANSLATION (chksum(pcal) = "a5a326e" /\ chksum(tla) = "fcd5d385")
VARIABLES Objs, pc

(* define statement *)
TypeOk == /\ \A o \in Objs: /\ o.k \in ObjKinds
                            /\ o.oid \in OIDs
                            /\ o.deleted \in BOOLEAN
          /\ \A x, y \in Objs: x = y \/ x.oid # y.oid


FreeOIDs == OIDs \ {o.oid : o \in Objs}


empty == [x \in {} |-> {}]


vars == << Objs, pc >>

ProcSet == ({"user"}) \cup ({"GC"}) \cup ({"RDC"})

Init == (* Global variables *)
        /\ Objs = {}
        /\ pc = [self \in ProcSet |-> CASE self \in {"user"} -> "UStart"
                                        [] self \in {"GC"} -> "GCStart"
                                        [] self \in {"RDC"} -> "RDStart"]

UStart(self) == /\ pc[self] = "UStart"
                /\ \/ /\ \E i \in FreeOIDs:
                           Objs' = (Objs \cup { [oid |-> i, k |-> "RD", deleted |-> FALSE, LI |-> nil] })
                   \/ /\ \E rd \in {o \in Objs: o.k = "RD" /\ o.deleted = FALSE}:
                           Objs' = ((Objs \ {rd}) \cup {[rd EXCEPT !.deleted = TRUE]})
                /\ pc' = [pc EXCEPT ![self] = "UStart"]

User(self) == UStart(self)

GCStart(self) == /\ pc[self] = "GCStart"
                 /\ \/ /\ TRUE
                    \/ /\ TRUE
                 /\ pc' = [pc EXCEPT ![self] = "Done"]
                 /\ Objs' = Objs

GarbageCollector(self) == GCStart(self)

RDStart(self) == /\ pc[self] = "RDStart"
                 /\ \/ /\ \E rd \in {o \in Objs: o.k = "RD"}:
                            \E i \in FreeOIDs:
                              Objs' = ((Objs \ {rd}) \cup { [oid |-> i, k |-> "VS", owner |-> rd.oid, deleted |-> FALSE], [rd EXCEPT !.LI = i] })
                    \/ /\ \E vs \in {o \in Objs: /\ o.k = "VS"
                                                 /\ o.deleted = FALSE
                                    
                                    
                                                 /\ o.oid \notin { rd.LI: rd \in {x \in Objs: x.k = "RD"} } }:
                            Objs' = ((Objs \ {vs}) \cup {[vs EXCEPT !.deleted = TRUE]})
                 /\ pc' = [pc EXCEPT ![self] = "RDStart"]

RDController(self) == RDStart(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {"user"}: User(self))
           \/ (\E self \in {"GC"}: GarbageCollector(self))
           \/ (\E self \in {"RDC"}: RDController(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
-----------------------------------------------------------------------------


=============================================================================
\* Modification History
\* Last modified Fri Feb 03 16:37:27 EST 2023 by jstrunk
\* Created Fri Feb 03 09:54:49 EST 2023 by jstrunk
