# Zlog - a distributed shared log for ceph

[![Build Status](https://travis-ci.org/noahdesu/zlog.svg)](https://travis-ci.org/noahdesu/zlog)

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

There is also support for asynchronous log operations. First create a new `Log::AioCompletion` object and then call `Log::AioAppend` to initiate the operation.

```c++
ceph::bufferlist bl; // data to append
uint64_t position;
Log::AioCompletion *c = Log::aio_create_completion();
log.AioAppend(c, bl, &position);
```

Then you can wait on the append to complete and verify success.

```c++
c->wait_for_complete();
assert(c->get_return_value() == 0); // success
std::cout << position << std::endl;
c->release(); // clean-up
```

Rather than waiting on the operation to complete, a callback can be specified when creating the completion object. We use an `AioState` object to keep track of the context. The callback, `aio_cb`, is shown below.

```c++
struct AioState {
  Log::AioCompletion *c;
  uint64_t position;
}

AioState *s = new AioState;
ceph::bufferlist bl; // data to append
s->c = Log::aio_create_completion(s, aio_cb);
log.AioAppend(c, bl, &s->position);
```

In the handler we print out the final position contained in the context and free up resources.

```c++
static void aio_cb(AioCompletion::completion_t cb, void *arg)
{
  AioState *s = (AioState*)arg;
  std::cout << s->position << std::endl;
  s->c->release();
  delete s;
}
```

## Build and Install

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
* cls_zlog (see below)

### Building cls_zlog

The current object interface in RADOS is incapable of expressing the access
methods required for an efficient implementation of the CORFU protocol (the
good news is this will likely change in the future).  However, RADOS
supports custom object interfaces through pluggable C++ modules which `zlog`
uses to add the necessary interfaces. The custom interface is referred to as
`cls_zlog` and it is implemented as two components: (1) a loadable RADOS
plugin that injects new behavior into the storage system, and (2) a
lightweight client library that hides the custom object interface
communication protocol. These two dependencies are currently maintained in the
`cls_zlog` Ceph branch located at
https://github.com/noahdesu/ceph/tree/cls_zlog. Building this branch will
produce both the RADOS server plugin and the client library.

If you are already familiar with building Ceph from source, then the
`cls_zlog` branch can be built without any additional dependencies, and it is
configured to automatically produce the `cls_zlog` shared libraries without
any special options. If you are not familiar with the process there is
documentation located at http://ceph.com/docs/master/install/build-ceph/. In
general, the process for building the `cls_zlog` dependency looks like this:

First clone the `zlog` Ceph repository and checkout the `cls_zlog` branch:

```
git clone --recursive https://github.com/noahdesu/ceph.git
cd ceph
git checkout cls_zlog
```

Next configure and build the tree:

```
./install-deps.sh
./autogen.sh
./configure
make -j4
```

Note that while you can build the entire Ceph tree, it is possible to only
build the `cls_zlog` components. This is very useful because building the
entire Ceph tree can take a significant amount of time:

```
cd src
make libcls_zlog.la
make libcls_zlog_client.la
```

That's it. Next we'll grab the `cls_zlog` artifacts and install them.

### Installing cls_zlog

Building the `zlog` project depends on the `cls_zlog` client library that we
just built above. We'll grab this dependency from the Ceph tree we just built
above and tell `./configure` about them using `CPPFLAGS` and `LDFLAGS`:

```
mkdir -p libcls_zlog_client/include/rados
mkdir -p libcls_zlog_client/lib
cp /path/to/ceph/src/.libs/libcls_zlog_client* libcls_zlog_client/lib
cp /path/to/ceph/src/cls/zlog/cls_zlog_client.h libcls_zlog_client/include/rados
CPPFLAGS=-Ilibcls_zlog_client/include LDFLAGS=-Llibcls_zlog_client/lib ./configure
make
```

You'll likely need to also export `LD_LIBRARY_PATH` to point at the location
where the `cls_zlog` client library was saved (e.g. the `libcls_zlog_client`
        directory we created in the snippet above). That's it for the `zlog`
client. Next we need to make sure the `cls_zlog` plugin is installed in Ceph.

If you just want to test `zlog` and don't want to use a full Ceph cluster, you
can use the Ceph developer mode to quickly start a Ceph cluster on a single
node from the source tree that you just built. See
http://ceph.com/docs/v0.86/dev/quick_guide/ for more information. In this case
you only need to install the `cls_zlog` client as the mini Ceph cluster will
automatically pick up the plugin when run from the source tree.

Installing the `cls_zlog` plugin is slightly more involved. For each OSD node
in your Ceph cluster there is a directory from which object interface plugins
are automatically loaded. Typically this is `/usr/lib/rados-classes/` or
`/usr/lib64/rados-classes/`. This directory will already exist if you have a
standard Ceph installation. Copy the `cls_zlog` plugin from the source tree we
built above into this directory on all Ceph OSD nodes:

```
cp /path/to/ceph/src/.libs/libcls_zlog.so* /usr/lib/rados-classes/
```

Once the plugin has been copied to a server the OSD processes on that node
should be restarted.

## References

* http://research.microsoft.com/pubs/157204/corfumain-final.pdf
* http://www.cs.cornell.edu/~taozou/sosp13/tangososp.pdf
* http://ceph.com
