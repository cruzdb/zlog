AM_CPPFLAGS = -I$(top_srcdir)/src/include

bin_PROGRAMS =
noinst_LIBRARIES =
lib_LTLIBRARIES =
noinst_LTLIBRARIES =
BUILT_SOURCES =
MOSTLYCLEANFILES =
dist_noinst_DATA =
include_HEADERS =

LIBPROTO = libzlogproto.la
LIBSEQ = libseqr.la
LIBZLOG = libzlog.la
LIBZSTATE = libzstate.la
LIBGTEST = libgtest.a
ZLOG_JAR = zlog.jar

include proto/Makefile.am
include libseq/Makefile.am
include libzlog/Makefile.am
include zstate/Makefile.am
include test/Makefile.am
include java/Makefile.am

bin_PROGRAMS += zlog-seqr
zlog_seqr_SOURCES = seqr-server.cc
zlog_seqr_CPPFLAGS = $(BOOST_CPPFLAGS) $(AM_CPPFLAGS)
zlog_seqr_LDFLAGS = $(BOOST_THREAD_LDFLAGS) $(BOOST_SYSTEM_LDFLAGS) $(BOOST_PROGRAM_OPTIONS_LDFLAGS)
zlog_seqr_LDADD = $(LIBPROTO) $(LIBZLOG) $(BOOST_THREAD_LIBS) $(BOOST_SYSTEM_LIBS) $(BOOST_PROGRAM_OPTIONS_LIBS)

bin_PROGRAMS += zlog-seqr-bench
zlog_seqr_bench_SOURCES = zlog-seqr-bench.cc
zlog_seqr_bench_CPPFLAGS = $(BOOST_CPPFLAGS) $(AM_CPPFLAGS)
zlog_seqr_bench_LDFLAGS = $(BOOST_THREAD_LDFLAGS) $(BOOST_SYSTEM_LDFLAGS) $(BOOST_PROGRAM_OPTIONS_LDFLAGS)
zlog_seqr_bench_LDADD = $(LIBSEQ) $(LIBZLOG) $(BOOST_THREAD_LIBS) $(BOOST_SYSTEM_LIBS) $(BOOST_PROGRAM_OPTIONS_LIBS)

bin_PROGRAMS += zlog-bench-ng
zlog_bench_ng_SOURCES = zlog-bench-ng.cc
zlog_bench_ng_CPPFLAGS = $(BOOST_CPPFLAGS) $(AM_CPPFLAGS)
zlog_bench_ng_LDFLAGS = $(BOOST_THREAD_LDFLAGS) $(BOOST_SYSTEM_LDFLAGS) $(BOOST_PROGRAM_OPTIONS_LDFLAGS)
zlog_bench_ng_LDADD = $(LIBSEQ) $(LIBZLOG) $(BOOST_THREAD_LIBS) $(BOOST_SYSTEM_LIBS) $(BOOST_PROGRAM_OPTIONS_LIBS)

bin_PROGRAMS += stream-stress
stream_stress_SOURCES = stream-stress.cc
stream_stress_CPPFLAGS = $(BOOST_CPPFLAGS) $(AM_CPPFLAGS)
stream_stress_LDFLAGS = $(BOOST_THREAD_LDFLAGS) $(BOOST_SYSTEM_LDFLAGS) $(BOOST_PROGRAM_OPTIONS_LDFLAGS)
stream_stress_LDADD = $(LIBSEQ) $(LIBZLOG) $(BOOST_THREAD_LIBS) $(BOOST_SYSTEM_LIBS) $(BOOST_PROGRAM_OPTIONS_LIBS)

bin_PROGRAMS += append-check
append_check_SOURCES = append-check.cc
append_check_CPPFLAGS = $(BOOST_CPPFLAGS) $(AM_CPPFLAGS)
append_check_LDFLAGS = $(BOOST_THREAD_LDFLAGS) $(BOOST_SYSTEM_LDFLAGS) $(BOOST_PROGRAM_OPTIONS_LDFLAGS)
append_check_LDADD = $(LIBSEQ) $(LIBZLOG) $(BOOST_THREAD_LIBS) $(BOOST_SYSTEM_LIBS) $(BOOST_PROGRAM_OPTIONS_LIBS)

bin_PROGRAMS += zlog
zlog_SOURCES = zlog-tool.cc
zlog_CPPFLAGS = $(BOOST_CPPFLAGS) $(AM_CPPFLAGS)
zlog_LDFLAGS = $(BOOST_THREAD_LDFLAGS) $(BOOST_SYSTEM_LDFLAGS) $(BOOST_PROGRAM_OPTIONS_LDFLAGS)
zlog_LDADD = $(LIBSEQ) $(LIBZLOG) $(BOOST_THREAD_LIBS) $(BOOST_SYSTEM_LIBS) $(BOOST_PROGRAM_OPTIONS_LIBS)
