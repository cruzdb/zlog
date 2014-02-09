bin_PROGRAMS =
noinst_LIBRARIES =
lib_LTLIBRARIES =
noinst_LTLIBRARIES =
BUILT_SOURCES =
MOSTLYCLEANFILES =
dist_noinst_DATA =

%.pb.cc %.pb.h: %.proto
	$(PROTOC) --proto_path=$(srcdir) --cpp_out=$(builddir) $^

BUILT_SOURCES += zlog.pb.h
MOSTLYCLEANFILES += zlog.pb.cc zlog.pb.h
dist_noinst_DATA += zlog.proto

noinst_LTLIBRARIES += libzlogproto.la
libzlogproto_la_SOURCES = zlog.pb.cc zlog.pb.h
libzlogproto_la_CXXFLAGS = $(PROTOBUF_CFLAGS)
libzlogproto_la_LIBADD = $(PROTOBUF_LIBS)

lib_LTLIBRARIES += libzlog.la
libzlog_la_SOURCES = libzlog.cc libzlog.h
libzlog_la_LIBADD = libzlogproto.la -lrados

include seqr/Makefile.am

### Tests

noinst_LIBRARIES += libgtest.a
libgtest_a_SOURCES = gtest/src/gtest-all.cc gtest/src/gtest_main.cc
libgtest_a_CPPFLAGS = -Igtest/include -Igtest

GTEST_CXXFLAGS = -I$(top_srcdir)/src/gtest/include
GTEST_LDADD = $(top_builddir)/src/libgtest.a -lpthread

bin_PROGRAMS += test_libzlog
test_libzlog_SOURCES = test_libzlog.cc
test_libzlog_CXXFLAGS = $(GTEST_CXXFLAGS)
test_libzlog_LDADD = $(GTEST_LDADD) libzlog.la -lrados
