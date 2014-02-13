bin_PROGRAMS += zlog-seqr
zlog_seqr_SOURCES = seqr/server.cc
zlog_seqr_CPPFLAGS = $(BOOST_CPPFLAGS)
zlog_seqr_LDFLAGS = $(BOOST_THREAD_LDFLAGS) $(BOOST_SYSTEM_LDFLAGS) $(BOOST_PROGRAM_OPTIONS_LDFLAGS)
zlog_seqr_LDADD = libzlogproto.la libzlog.la $(BOOST_THREAD_LIBS) $(BOOST_SYSTEM_LIBS) $(BOOST_PROGRAM_OPTIONS_LIBS)

noinst_LTLIBRARIES += libseqr.la
libseqr_la_SOURCES = seqr/libseqr.cc seqr/libseqr.h
libseqr_la_LIBADD = libzlogproto.la
