------------------------------- MODULE zlog -------------------------------

EXTENDS Integers, TLC, Sequences

CONSTANTS O, C

Objects   == 1..O
Clients   == O+1..O+C
Sequencer == O+C+1
SeqReboot == O+C+2
Procs     == 1..O+C+2

CONSTANTS OpWrite, OpMaxPos, OpSeal
CONSTANTS ReplyOk, ReplyWritten, ReplyStaleEpoch

Max(S) == CHOOSE i \in S : \A j \in S : j \leq i

(*
--algorithm zlog
{
    variable
        network = [p \in Procs |-> <<>>],
        entries = [i \in Objects |-> [j \in {} |-> <<>>]],
        seq = 0,
        real_epoch = 0;
        
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
    s2:     Send(msg.src, [reply |-> ReplyOk,
                           pos   |-> seq]);
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
    variable objects, msg, results, new_epoch;
    {
    r1: while (TRUE) {
            new_epoch := real_epoch + 1;
            objects := Objects;
    r2:     while (objects # {}) {
                with (object \in objects) {
                    Send(object, [src   |-> SeqReboot,
                                  op    |-> OpSeal,
                                  epoch |-> new_epoch]);
                                  
                    objects := objects \ {object};
                };
    r3:         Receive(SeqReboot, msg);
                assert(msg.reply = ReplyOk);
            };            
            results := {};
            objects := Objects;
    r4:     while (objects # {}) {
                with (object \in objects) {
                    Send(object, [src   |-> SeqReboot,
                                  op    |-> OpMaxPos,
                                  epoch |-> new_epoch]);
                    objects := objects \ {object};
                };
    r5:         Receive(SeqReboot, msg);
                assert(msg.reply = ReplyOk);
                results := results \cup {msg.maxpos};
            };
            seq := Max(results) + 1;
            real_epoch := new_epoch;
        }
    }

    (***********************************************************************)
    (* Objects provide durable, fault-tolerant storage.  Each object acts  *)
    (* as an RPC server with sequential semantics.  An example are RADOS   *)
    (* objects that are 3-way replicated and provide strong consistency.   *)
    (***********************************************************************)
    process (o \in Objects)
    variable msg,
             epoch = -1; \* initialize as unspecified
    {
    o1: while (TRUE) {
            Receive(self, msg);

            (***************************************************************)
            (* Write an entry at the specified position, enforcing         *)
            (* write-once semantics by returning an error if the position  *)
            (* has been written to or invalidated.                         *)
            (***************************************************************)
    o2:     if (msg.op = OpWrite) {
                if (epoch >= 0 /\ msg.epoch < epoch) { \* use equality?
                    Send(msg.src, [reply |-> ReplyStaleEpoch]);
                    goto o1;
                } else if (msg.pos \in DOMAIN entries[self]) {
                    Send(msg.src, [reply |-> ReplyWritten]);
                } else {
                    entries := [entries EXCEPT ![self] = @ @@ msg.pos :> <<msg.pos>>];
                    Send(msg.src, [reply |-> ReplyOk]);
                }
            
            (***************************************************************)
            (* Return the maximum position that has been written to for    *)
            (* this object.  If no position has been written to, a         *)
            (* sentinal value is returned indicating this state.           *)
            (***************************************************************)
            } else if (msg.op = OpMaxPos) {
                assert(epoch >= 0); \* should only be called after sealing
                if (msg.epoch # epoch) {
                    Send(msg.src, [reply |-> ReplyStaleEpoch]);
                    goto o1;
                } else if (DOMAIN entries[self] = {}) {
                    Send(msg.src, [reply  |-> ReplyOk,
                                   maxpos |-> -1]);
                } else {
                    Send(msg.src, [reply  |-> ReplyOk,
                                   maxpos |-> Max(DOMAIN entries[self])]);
                }

            (***************************************************************)
            (* asdf                                                        *)
            (***************************************************************)
            } else if (msg.op = OpSeal) {
                assert(msg.epoch >= 0);
                if (epoch >= 0 /\ msg.epoch <= epoch) { \* use equality?
                    Send(msg.src, [reply |-> ReplyStaleEpoch]);
                    goto o1;
                } else {
                    Send(msg.src, [reply |-> ReplyOk]);
                    epoch := msg.epoch;
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
    c4: Receive(self, msg);
        assert(msg.reply = ReplyOk);
    }
}
*)
