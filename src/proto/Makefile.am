%.pb.cc %.pb.h: %.proto
	$(PROTOC) --proto_path=$(srcdir)/proto --cpp_out=$(builddir)/proto $^

BUILT_SOURCES += proto/zlog.pb.h
MOSTLYCLEANFILES += proto/zlog.pb.cc proto/zlog.pb.h
dist_noinst_DATA += proto/zlog.proto

noinst_LTLIBRARIES += libzlogproto.la
libzlogproto_la_SOURCES = proto/zlog.pb.cc proto/zlog.pb.h
libzlogproto_la_CXXFLAGS = $(PROTOBUF_CFLAGS)
libzlogproto_la_LIBADD = $(PROTOBUF_LIBS)
