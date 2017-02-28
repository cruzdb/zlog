=============
Using the API
=============

The ``zlog`` library provides a high-performance, strongly consistent shared-log
abstraction, and may be used directly as a basis for a
distributed service or application. Additionally, the ``zlog`` project provides a
transactional key-value store engine built on top of the log service.

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

==========================
Key-Value Storage Engine
==========================

The ``zlog`` project provides a distributed key-value storage engine that
operates on top of the log service. The engine provides basic ``get``, ``put``,
``delete`` operations as well as support for snapshots, iterators, and
transactions. The database uses an MVCC scheme so queries over read-only
snapshots will not affect on-going transactions.

The database is created by provided a pointer to a log (see above for creating
a log).

.. code-block:: c++

	{
	  // open the database
	  auto db = DB::Open(log);
	
	  // run the optimistic transaction
	  auto txn = db.BeginTransaction();
	  txn.Put("67", "val");
	  txn.Commit();
	}

Multiple operations may be combined in a single transaction:

.. code-block:: c++

	// PUT: 94, 06
	auto txn = db.BeginTransaction();
	txn.Put("94", "val");
	txn.Put("06", "val");
	txn.Commit();

and transactions can contain any combination of ``get``, ``put``, and ``delete`` operations:

.. code-block:: c++

	...
	txn = db.BeginTransaction();
	txn.Put("93", "val");
	
	std::string data;
	txn.Get("88", &data);
	if (data == "foo")
	  txn.Delete("76");
	
	txn.Commit();
	...

## Iteration and Snapshots

The key-value store exposes an iterator and can operate on a snapshot of the
database. The following code snippet shows how to print all key-value pairs in
the database at the time the iterator is created (any modification that occur
after the iterator is created will not seen).

.. code-block:: c++

	auto it = db.NewIterator();
	while (it.Valid()) {
	  std::cout << it.key() << " " it.value() << std::endl;
	  it.Next();
	}

By default the ``NewIterator`` method will access the latest version of the
database. A snapshot can be taken and later read by an iterator:

.. code-block:: c++

	auto ss = db.GetSnapshot();
	
	// modify db ...
	
	// this iterator will not observe the previous modifications
	auto it = db.NewIterator(ss);
	while (it.Valid()) {
	  std::cout << it.key() << " " it.value() << std::endl;
	  it.Next();
	}

Here is a summary of the full iterator interface. I've removed the comments as
the method names should be self-explanatory:
 
.. code-block:: c++

	class Iterator {
	 public:
	  Iterator(Snapshot snapshot);
	
	  // true iff iterator points to a valid entry
	  bool Valid() const;
	
	  // reposition the iterator
	  void SeekToFirst();
	  void SeekToLast();
	  void Seek(const std::string& target);
	
	  // navigation
	  void Next();
	  void Prev();
	
	  // retrieve the current key-value entry
	  std::string key() const;
	  std::string value() const;
	
	  int status() const;
	
	  ...
	};
