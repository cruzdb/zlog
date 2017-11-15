#define MAX_ENTRIES 5
#define NUM_OBJECTS 2

mtype {
  ok,
  write
};

// channel for requesting maximum position from object
chan maxpos_req[NUM_OBJECTS] = [0] of { chan };

// channel for object entry operations (read, write, etc...)
chan entry_req[NUM_OBJECTS] = [0] of { mtype, chan, byte };

// channel for sequencer next position requests
chan nextpos_req = [0] of { chan };

#define p2o(pos) (pos % NUM_OBJECTS)

proctype Object(byte id) {
  chan reply;

  // log entries managed by this object
  byte entries[MAX_ENTRIES];

  // handling maxpos requests
  byte i, max;
  bool bare;

  // handling write requests
  byte pos;

end:
  do
  // handle maxpos request. if bare, pos is undefined
  :: maxpos_req[id] ? reply ->
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
    reply ! bare, max

  // handle write request
  :: entry_req[id] ? write(reply, pos) ->
    if
    :: entries[pos] > 0 ->
      assert(false)
    :: else ->
      entries[pos] = 1
      reply ! ok
    fi
  od;
}

proctype Sequencer() {
  chan maxpos_reply = [NUM_OBJECTS] of { bool, int };
  chan nextpos_reply;

  // log tail position
  byte seq;

  // initialization
  byte i, max;
  bool bare;

  // initialization. phase 1: send maxpos requests
  for (i in maxpos_req) {
    maxpos_req[i] ! maxpos_reply
  }

  // initialization. phase 2: reduce replies
  seq = 0;
  for (i in maxpos_req) {
    maxpos_reply ? bare, max;
    if
    :: !bare && (max + 1) > seq
      -> seq = max + 1
    :: else -> skip
    fi;
  }

end:
  do
  // handle nextpos request
  :: nextpos_req ? nextpos_reply ->
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

  nextpos_req ! reply
  reply ? pos
  oid = p2o(pos)
  entry_req[oid] ! write(entry_reply, pos)
  entry_reply ? status;
  printf("write %d -> %e\n", pos, status)

  nextpos_req ! reply
  reply ? pos
  oid = p2o(pos)
  entry_req[oid] ! write(entry_reply, pos)
  entry_reply ? status;
  printf("write %d -> %e\n", pos, status)
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
