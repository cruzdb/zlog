Zlog - a distributed shared log for ceph
===

Zlog is a strongly consistent shared log designed to run on top of Ceph.
Specifically, it is an implementation of the CORFU protocol adapted for RADOS,
the distributed object storage system that powers Ceph.

## Example

First create a connection to the sequencer service:

```c++
zlog::SeqrClient seqr("localhost", "5678");
```

Next create a brand new log. A given log is striped across objects in a RADOS
pool.  When you create a new log provide a handle to the pool, as well as a
striping width and a name for the log.

```c++
const int stripe_width = 100;
zlog::Log log;
zlog::Log::Create(ioctx, "mylog", stripe_width, &seqr, log);
```

Now the log is available to use. In the following code snippet a string is
appended to the log which returns the position at which the string was stored.
Finally the string at the reported position is read back and verified.

```c++
ceph::bufferlist bl_in;
bl_in.append("My first log entry");

uint64_t pos;
log.Append(bl_in, &pos);

ceph::bufferlist bl_out;
log.Read(pos, bl_out);

assert(bl_in == bl_out);
```

## Building

```bash
autoreconf -ivf
./configure
make
```

### Dependencies

* boost-devel
* protobuf-compiler
* protobuf-devel
* librados2
* ceph-devel

## References

* http://research.microsoft.com/pubs/157204/corfumain-final.pdf
* http://www.cs.cornell.edu/~taozou/sosp13/tangososp.pdf
* http://ceph.com
