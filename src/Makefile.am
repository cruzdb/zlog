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

bin_PROGRAMS += zlog-seqr
zlog_seqr_SOURCES = seqr-server.cc
zlog_seqr_CPPFLAGS = $(BOOST_CPPFLAGS)
zlog_seqr_LDFLAGS = $(BOOST_THREAD_LDFLAGS) $(BOOST_SYSTEM_LDFLAGS) $(BOOST_PROGRAM_OPTIONS_LDFLAGS)
zlog_seqr_LDADD = libzlogproto.la libzlog.la $(BOOST_THREAD_LIBS) $(BOOST_SYSTEM_LIBS) $(BOOST_PROGRAM_OPTIONS_LIBS)

bin_PROGRAMS += zlog-seqr-bench
zlog_seqr_bench_SOURCES = zlog-seqr-bench.cc
zlog_seqr_bench_CPPFLAGS = $(BOOST_CPPFLAGS)
zlog_seqr_bench_LDFLAGS = $(BOOST_THREAD_LDFLAGS) $(BOOST_SYSTEM_LDFLAGS) $(BOOST_PROGRAM_OPTIONS_LDFLAGS)
zlog_seqr_bench_LDADD = libseqr.la libzlog.la $(BOOST_THREAD_LIBS) $(BOOST_SYSTEM_LIBS) $(BOOST_PROGRAM_OPTIONS_LIBS)

bin_PROGRAMS += zlog-bench-ng
zlog_bench_ng_SOURCES = zlog-bench-ng.cc
zlog_bench_ng_CPPFLAGS = $(BOOST_CPPFLAGS)
zlog_bench_ng_LDFLAGS = $(BOOST_THREAD_LDFLAGS) $(BOOST_SYSTEM_LDFLAGS) $(BOOST_PROGRAM_OPTIONS_LDFLAGS)
zlog_bench_ng_LDADD = libseqr.la libzlog.la $(BOOST_THREAD_LIBS) $(BOOST_SYSTEM_LIBS) $(BOOST_PROGRAM_OPTIONS_LIBS)

noinst_LTLIBRARIES += libseqr.la
libseqr_la_SOURCES = libseqr.cc libseqr.h
libseqr_la_LIBADD = libzlogproto.la

lib_LTLIBRARIES += libzlog.la
libzlog_la_SOURCES = libzlog.cc libzlog.h
libzlog_la_CPPFLAGS = $(BOOST_CPPFLAGS)
libzlog_la_LDFLAGS = $(BOOST_SYSTEM_LDFLAGS)
libzlog_la_LIBADD = libseqr.la -lcls_zlog_client $(BOOST_SYSTEM_LIBS)

lib_LTLIBRARIES += libzstate.la
libzstate_la_SOURCES = zstate/skytype.cc
libzstate_la_LIBADD = libzlog.la

### Tests

noinst_LIBRARIES += libgtest.a
libgtest_a_SOURCES = gtest/src/gtest-all.cc gtest/src/gtest_main.cc
libgtest_a_CPPFLAGS = -Igtest/include -Igtest

GTEST_CXXFLAGS = -I$(top_srcdir)/src/gtest/include
GTEST_LDADD = $(top_builddir)/src/libgtest.a -lpthread

bin_PROGRAMS += test
test_SOURCES = test.cc
test_CXXFLAGS = $(GTEST_CXXFLAGS)
test_LDADD = libzlog.la $(GTEST_LDADD) $(BOOST_SYSTEM_LIBS)

bin_PROGRAMS += zstate-test
zstate_test_SOURCES = zstate/test.cc
zstate_test_CXXFLAGS = $(GTEST_CXXFLAGS)
zstate_test_LDADD = libzlog.la libzstate.la $(GTEST_LDADD) $(BOOST_THREAD_LIBS) $(BOOST_SYSTEM_LIBS)
