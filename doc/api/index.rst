=============
Using the API
=============

The ``zlog`` library provides a high-performance, strongly consistent shared-log
abstraction, and may be used directly as a basis for a
distributed service or application.

##################
Shared-Log Service
##################

A log is created by first providing an instance of a storage backend. We
provide here an example of instantiating an instance of the in-memory backend.

*******************
Development Backend
*******************

The following code snippet creates a new log instance using the development storage backend.

.. code-block:: c++

	#include <zlog/log.h>
	#include <zlog/backend/ram.h>
	
	Backend *backend = new RAMBackend();
	SeqrClient *seqclient = new FakeSeqrClient();
	
	zlog::Log *log;
	int ret = zlog::Log::Create(backend, "mylog", seqclient, &log);

Now the log is ready to use. Next we'll go over the basic log operations.

####################
Appending to the log
####################

In the following code snippet a string is appended to the log which returns the
position at which the string was stored.  Finally the string at the reported
position is read back and verified.

.. code-block:: c++

	const std::string input = "My first log entry";

	uint64_t pos;
	int ret = log.Append(Slice(input), &pos);
	assert(ret == 0);

Once an append occurs it is immutable and cannot be changed (the exception to
this rule is garbage collection. see below for the ``trim`` operation).

#######################
Reading from the log
#######################

Any position in the log may be read. If valid data exists it will be returned,
and log entries that have not been written or have been filled or garbage
collected will return appropriate error messages. In the following snippet we
verify the data written in the previous example.

.. code-block:: c++

	std::string output;
	int ret = log.Read(pos, &output);
	assert(ret == 0);
	
	assert(input == ouput);

##############
Check log tail
##############

The ``Log::CheckTail`` method is used to query the sequencer service about the
current tail of the log. The position returned by the ``Log::CheckTail`` method
is the position that the next append will be written to. This method is useful
determining how much of the log must be read to be up-to-date with other
processes in the system.

.. code-block:: c++

	uint64_t tail;
	int ret = log.CheckTail(&tail);
	assert(ret == 0);
	
	std::cout << "next append position: " << tail << std::endl;

######################
Filling a log position
######################

The ``fill`` operation is a light-weight mechanism for invalidating a log entry
and is analogous to an application writing data to a log entry that all other
clients would consider a *junk* value. This is useful when clients are
processing the log in strict serial order: if a writer is slow a reader may
fill a log position in order to make forward progress. Other readers will
always skip the position without concern for missing an entry because any
writer to the filled position will be forced to retry an append.

.. code-block:: c++

	std::string output;
	int ret = log.Read(pos, &output);
	if (ret == zlog::NOT_WRITTEN) {
	  ret = log.Fill(pos);
	  if (ret == zlog::READ_ONLY) {
	    // try the read again. it was a race
	  } else {
	    // position filled. read next position
	  }
	}

################
Trimming the log
################

In order to reclaim space the log supports a ``trim`` method that marks a log
position for garbage collection. Any readers to the position will receive an
error indicated that the log position has been invalidated. It is the
responsibility of the application to ensure correctness (e.g. no pointers to
the trimmed position exist).

.. code-block:: c++

	int ret = log.Trim(pos);
	assert(ret == 0);

#######################
Asynchronous Operations
#######################

Asynchronous versions of the log operations are also available. The ``zlog``
library provides a ``Log::AioCompletion`` type for managing the context of an
asynchronous operation. First create an instance of ``Log::AioCompletion`` using
``Log::aio_create_completion()``:

.. code-block:: c++

	Log::AioCompletion *c = Log::aio_create_completion();
	
	const std::string input = "Hello log";
	uint64_t position;
	
	int ret = log.AioAppend(c, Slice(input), &position);
	assert(ret == 0);

After ``log::AioAppend`` returns the completion object can be used to determine
the state of the append operation.

.. code-block:: c++

	c->WaitForComplete(); // block until the operation finishes
	assert(c->ReturnValue() == 0); // success
	std::cout << "appended data at: " << position << std:::endl;
	delete c; // clean-up

######################
Asynchronous Callbacks
######################

Rather than waiting on the operation to complete, a callback can be specified
when creating the completion object. In the following example we use an
``AioState`` type to keep track of the context. In the following example an
asynchronous read is issued and the data read is printed to standard out in the
callback handler.

First define the callback context and the callback handler:

.. code-block:: c++

	struct AioState {
	  Log::AioCompletion *c;
	  std::string output;
	}
	
	static void aio_cb(AioState *state)
	{
	  assert(state->c->ReturnValue() == 0); // success?
	
	  std::cout << "data read: " << state->output << std::endl;
	
	  delete state->c;
	  delete state;
	}

Now create the context objects and issue the asynchronous read:

.. code-block:: c++

	AioState *state = new AioState;
	state->c = zlog::Log::aio_create_completion(std::bind(aio_cb, state));
	int ret = log->AioRead(pos, state->c, &state->data);
	assert(ret == 0);
	
	// do other stuff while I/O completes

##################
Stream Abstraction
##################

.. note:: work-in-progress. see src/include/zlog/stream.h

#############
Java Bindings
#############

View the auto-generated `JavaDoc pages for the ZLog Java bindings <java/>`_.
