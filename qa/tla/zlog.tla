-------------------------------- MODULE zlog --------------------------------
\* fixed set of objects. one sequencer that can fail and restart.

EXTENDS Integers

CONSTANTS Values, \* appended to the log
          Objects \* storage devices. fault-tolerant, and consistent.
          

\* valid log positions are integers >= 0
LogPositions == Nat \cup {0}

VARIABLES msgs, seq

Send(m) == msgs' = msgs \cup {m}

Init == /\ msgs = {}

Messages == [type : {"a1"}, val : Values]

(***************************************************************************)
(* Append Phase 1: A client requests a position from the sequencer by      *)
(* sending a request message.  The value in the message is not used by the *)
(* sequencer.  It is used to distinguish one request from another in the   *)
(* set of all messages.                                                    *)
(***************************************************************************)
Append1(v) == /\ ~ \E m \in msgs : (m.type = "a1") /\ (m.val = v)
              /\ Send([type |-> "a1", val |-> v])
              /\ UNCHANGED <<seq>>

(***************************************************************************)
(* Append Phase 2: If a client receives a response from the sequencer, it  *)
(* sends a write request message to the object that is mapped by the       *)
(* response from the sequencer and the current known system configuration. *)
(***************************************************************************)

(***************************************************************************)
(* Append Phase 3: If a client receives a response from an object, and the *)
(* response indicates that the log position is read-only, then retry the   *)
(* append operation starting from phase 1.                                 *)
(***************************************************************************)

(***************************************************************************
Sequence Request: If the sequencer receives a request 
 ***************************************************************************)
Sequence ==
  \E m \in msgs :
    /\ m.type = "a1"
    /\ ~ \E rm \in msgs : (rm.type = "s") /\ (rm.val = m.val)
    /\ Send([type |-> "s", val |-> m.val, seq |-> seq])
    /\ seq' = seq + 1

=============================================================================
\* Modification History
\* Last modified Sat Sep 30 16:37:18 PDT 2017 by nwatkins
\* Created Sat Sep 30 14:32:25 PDT 2017 by nwatkins
