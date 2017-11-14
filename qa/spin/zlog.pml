#define MAX_ENTRIES 5
#define NUM_OBJECTS 2

mtype {
  maxpos
};

chan object_request[NUM_OBJECTS] = [0] of { mtype, chan };

// entries:
//   0: unwritten position
//
proctype Object(chan request) {
  byte entries[MAX_ENTRIES];
  chan reply;

  entries[2] = 1;

end:
  do
  // handle maxpos request. the (empty, maxpos) tuple is returned. the value of
  // maxpos is undefined if the object is empty.
  :: request ? maxpos(reply) ->
    int i, max
    bool bare = true
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
    reply ! bare, max
  od;
}

proctype Sequencer() {
  bool bare;
  int i, max;
  int seq;

  // sequencer initialization. send a maxpos request to each object.
  chan seq_reply = [0] of { bool, int };
  for (i in object_request) {
    object_request[i] ! maxpos(seq_reply)
    seq_reply ? bare, max
    if
    :: bare -> skip
    :: else ->
      if
      :: (max + 1) > seq -> seq = max + 1
      :: else -> skip
      fi
    fi
  }
  printf("COUNT %d\n", seq)
}

init {
  atomic {
    run Object(object_request[0]);
    run Object(object_request[1]);
    run Sequencer();
  }
}
