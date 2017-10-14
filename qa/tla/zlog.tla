------------------------------- MODULE zlog -------------------------------

EXTENDS Integers, TLC, Sequences

CONSTANTS O, C

Objects   == 1..O
Clients   == O+1..O+C
Sequencer == O+C+1
SeqReboot == O+C+2
Procs     == 1..O+C+2

CONSTANTS OpWrite, OpMaxPos

Max(S) == CHOOSE i \in S : \A j \in S : j \leq i

(*
--algorithm zlog
{
    variable
        network = [p \in Procs |-> <<>>],
        entries = [i \in Objects |-> [j \in {} |-> <<>>]],
        seq = 0;
        
    macro Send(proc, m) {
        network := [network EXCEPT ![proc] = Append(@, m)];
    }

    macro Receive(proc, msg) {
        await Len(network[proc]) > 0;
        msg := Head(network[proc]);
        network := [network EXCEPT ![proc] = Tail(@)];
    }

    (***********************************************************************)
    (* The current set of states the sequencer can be in are both          *)
    (* compatible with the sequencer reboot process and points at which it *)
    (* can reset the sequencer state.  Make sure to coordinate changes in  *)
    (* either process to remain compatible.                                *)
    (***********************************************************************)
    process (s = Sequencer)
    variable msg = <<>>;
    {
    s1: while (TRUE) {
            Receive(Sequencer, msg);
    s2:     Send(msg.src, [pos |-> seq]);
            seq := seq + 1;
        }
    }
    
    (***********************************************************************)
    (* Simulate a restart of the sequencer process.  When a sequencer      *)
    (* starts it calculates the maximum position in the log to reseed its  *)
    (* sequence state.  This is done by querying each storage object and   *)
    (* calculating the global maximum.  A sequencer may crash at any       *)
    (* moment, hence the infinite loop.                                    *)
    (***********************************************************************)
    process (r = SeqReboot)
    variable objects, msg, results;
    {
    r1: while (TRUE) {
            results := {};
            objects := Objects;
    r2:     while (objects # {}) {
                with (object \in objects) {
                    Send(object, [src |-> SeqReboot, op |-> OpMaxPos]);
                    objects := objects \ {object};
                };
    r3:         Receive(SeqReboot, msg);
                results := results \cup {msg.maxpos};
            };
            seq := Max(results) + 1;
        }
    }

    (***********************************************************************)
    (* Objects provide durable, fault-tolerant storage.  Each object acts  *)
    (* as an RPC server with sequential semantics.  An example are RADOS   *)
    (* objects that are 3-way replicated and provide strong consistency.   *)
    (***********************************************************************)
    process (o \in Objects)
    variable msg = <<>>;
    {
    o1: while (TRUE) {
            Receive(self, msg);
            
            (***************************************************************)
            (* Write an entry at the specified position, enforcing         *)
            (* write-once semantics by returning an error if the position  *)
            (* has been written to or invalidated.                         *)
            (***************************************************************)
    o2:     if (msg.op = OpWrite) {
                if (msg.pos \in DOMAIN entries[self]) {
                    assert FALSE; \* temporary
                    Send(msg.src, [op |-> 1]);
                } else {
                    entries := [entries EXCEPT ![self] = @ @@ msg.pos :> <<msg.pos>>];
                    Send(msg.src, [op |-> 2]);
                }
            
            (***************************************************************)
            (* Return the maximum position that has been written to for    *)
            (* this object.  If no position has been written to, a         *)
            (* sentinal value is returned indicating this state.           *)
            (***************************************************************)
            } else if (msg.op = OpMaxPos) {
                if (DOMAIN entries[self] = {}) {
                    Send(msg.src, [maxpos |-> -1]);
                } else {
                    Send(msg.src, [maxpos |-> Max(DOMAIN entries[self])]);
                }
            }
        }
    }

    process (c \in Clients)
    variable oid = -1,
             pos = -1,
             msg = <<>>;
    {
    \* request position from sequencer
    c1: Send(Sequencer, [src |-> self]);
    c2: Receive(self, msg);

    \* send write request to target object
    c3: pos := msg.pos;
        oid := (pos % O) + 1;
        Send(oid, [src |-> self, op |-> OpWrite, pos |-> pos]);
    }
}
*)
