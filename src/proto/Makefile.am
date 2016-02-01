%.pb.cc %.pb.h: %.proto
	$(PROTOC) --proto_path=$(srcdir) --cpp_out=$(builddir) $^

BUILT_SOURCES = zlog.pb.h
MOSTLYCLEANFILES = zlog.pb.cc zlog.pb.h
dist_noinst_DATA = zlog.proto

noinst_LTLIBRARIES = libzlogproto.la
libzlogproto_la_SOURCES = zlog.pb.cc zlog.pb.h
libzlogproto_la_CXXFLAGS = $(PROTOBUF_CFLAGS)
libzlogproto_la_LIBADD = $(PROTOBUF_LIBS)
