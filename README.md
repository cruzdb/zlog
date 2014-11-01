Zlog - a distributed shared log for ceph
===

Zlog is a strongly consistent shared log designed to run on top of Ceph.
Specifically, it is an implementation of the CORFU protocol adapted for RADOS,
the distributed object storage system that powers Ceph.

More information:

* Design: http://noahdesu.github.io/2014/10/26/corfu-on-ceph.html

This project uses Semantic Versioning (http://semver.org/).

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
* libcls_zlog_client

The `libcls_zlog_client` dependency is currently a hassle to resolve because
the library is built in the `zlog` branch of the Ceph tree. The `zlog` branch
is located at http://github.com/noahdesu/ceph/tree/cls_zlog and building this
tree will automatically build the `libcls_zlog_client` library.

Once the library is built the `libcls_zlog_client` header will be located at
`src/cls/zlog/` and the shared library will be located at `src/.libs`. Either
reference these paths directly or copy the libraries to a new directory. In
either case, set `CPPFLAGS` and `LDFLAGS` before configuring and the depenency
should be resolved correctly.

**A nice enhancement would be to use Protocol Buffers to implement the
message encoding in `libcls_zlog_client`. This would allow us to have a
dependency on Protocol Buffers when building the `zlog` Ceph branch but would
eliminate the above process for resolving the client library dependency.**

## References

* http://research.microsoft.com/pubs/157204/corfumain-final.pdf
* http://www.cs.cornell.edu/~taozou/sosp13/tangososp.pdf
* http://ceph.com
