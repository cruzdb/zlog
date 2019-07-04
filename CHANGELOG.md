# Pending

# v0.6.0

* separate view and epoch-versioned-view abstractions
* use a scalable view / objectmap implementation
* moved away from protocol buffers to use only flatbuffers
* implemented a large set of unit test coverage for views
* initialize first stripe for new logs

# v0.5.0

* be/ceph: added support for controlling omap vs bytestream storage
* be/ceph: remove protocol buffers dependency from cls_zlog
* cli: basic cli infrastructure added
* be/lmdb: store unique id in the database to avoid duplicate ids
* be/bench: added simple direct backend benchmark / workload generator
* zlog clients are now registered as a rados application with ceph backend
* switched to the apache 2.0 license
* garbage collection for trimming

# v0.4.0

The first release in a serious effort to move towards a v1.0.0 release. This
version focused on code simplification and stability. In particular, this
release contains a simplified async I/O implementation, single-writer only (i.e.
no sequencer), simplified stripe and view handling, and a reworked Ceph storage
backend.
