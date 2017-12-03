#define MAX_ENTRIES 5
#define NUM_OBJECTS 2

mtype {
  ok,
  write,
  stale_epoch,

  maxpos,
  seal
};

// channel for requesting maximum position from object
chan seal_req[NUM_OBJECTS] = [0] of { mtype, chan, byte };

// channel for object entry operations (read, write, etc...)
chan entry_req[NUM_OBJECTS] = [0] of { mtype, chan, byte, byte };

// channel for sequencer next position requests
chan nextpos_req = [0] of { chan };

// TODO: this epoch value must be replaced by an oracle service such as paxos
// which also manages the system view state. for now we just want it to
// increment each time the sequencer restarts.
byte global_epoch = 0;

#define p2o(pos) (pos % NUM_OBJECTS)

proctype Object(byte id) {
  chan reply;

  // log entries managed by this object
  byte entries[MAX_ENTRIES];

  // handling maxpos requests
  byte i, max;
  bool bare;

  // handling entry requests
  byte pos;

  // epoch guards and sealing
  bool has_epoch = false;
  byte obj_epoch;
  byte req_epoch;

end:
  do
  // handle seal request
  :: seal_req[id] ? seal(reply, req_epoch) ->
    if
    :: has_epoch && (req_epoch <= obj_epoch) -> assert(false)
    :: else ->
      d_step {
        obj_epoch = req_epoch
        has_epoch = true
      }
      reply ! ok
    fi

  // handle maxpos request. if bare, pos is undefined
  :: seal_req[id] ? maxpos(reply, req_epoch) ->
    assert(has_epoch)
    if
    :: req_epoch != obj_epoch -> assert(false)
    :: else ->
      d_step {
        bare = true
        for (i in entries) {
          if
          :: entries[i] > 0 ->
            bare = false
            if
            :: i > max -> max = i
            :: else -> skip
            fi
          :: else -> skip
          fi
        }
      }
      reply ! ok, bare, max
    fi

  // handle write request
  :: entry_req[id] ? write(reply, req_epoch, pos) ->
    if
    :: has_epoch && (req_epoch < obj_epoch) -> reply ! stale_epoch
    :: else ->
      if
      :: entries[pos] > 0 -> assert(false)
      :: else ->
        entries[pos] = 1
        reply ! ok
      fi
    fi
  od;
}

proctype Sequencer() {
  chan seal_reply = [NUM_OBJECTS] of { mtype };
  chan maxpos_reply = [NUM_OBJECTS] of { mtype, bool, byte };
  chan nextpos_reply;
  mtype status

  // log tail position
  byte seq;

  // initialization
  byte i, max;
  bool bare;
  byte next_epoch;
  byte init_count = 0;

  do
  // initialization
  :: true && init_count < 5 ->
    next_epoch = global_epoch + 1

    // phase 1: seal objects
    for (i in seal_req) {
      seal_req[i] ! seal(seal_reply, next_epoch)
    }

    for (i in seal_req) {
      seal_reply ? status
      assert(status == ok)
    }

    // phase 2: dispatch maxpos request to objects
    for (i in seal_req) {
      seal_req[i] ! maxpos(maxpos_reply, next_epoch)
    }

    // phase 3: reduce maxpos requests to init val
    seq = 0;
    for (i in seal_req) {
      maxpos_reply ? status, bare, max;
      assert(status == ok)
      if
      :: !bare && (max + 1) > seq
        -> seq = max + 1
      :: else -> skip
      fi;
    }

    // TODO: far more complex. need a separate process to manage the view state,
    // but right now the epoch value is the view state.
    global_epoch = next_epoch;

    init_count++

  // handle nextpos request
  :: init_count > 0 ->
end:
    nextpos_req ? nextpos_reply
    nextpos_reply ! seq
    seq++
  od;
}

proctype Client() {
  byte pos
  byte oid
  chan reply = [0] of { byte }
  chan entry_reply = [0] of { mtype };
  mtype status;

  byte epoch = global_epoch

write0:
  nextpos_req ! reply
  reply ? pos
  oid = p2o(pos)
  entry_req[oid] ! write(entry_reply, epoch, pos)
  entry_reply ? status;
  if
  :: status == stale_epoch ->
    epoch = global_epoch
    goto write0
  :: else -> skip
  fi
  assert(status == ok)

write1:
  nextpos_req ! reply
  reply ? pos
  oid = p2o(pos)
  entry_req[oid] ! write(entry_reply, epoch, pos)
  entry_reply ? status;
  if
  :: status == stale_epoch ->
    epoch = global_epoch
    goto write1
  :: else -> skip
  fi
  assert(status == ok)
}

init {
  byte i;
  atomic {
    for (i : 0 .. (NUM_OBJECTS-1)) {
      run Object(i)
    }
    run Sequencer();
    run Client();
  }
}
