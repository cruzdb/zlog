lib_LTLIBRARIES += libzlog.la

libzlog_la_SOURCES = \
	libzlog/log_impl.cc \
	libzlog/log_impl.h \
	libzlog/stream.cc \
	libzlog/aio.cc \
	libzlog/stripe_history.cc \
	libzlog/stripe_history.h \
	libzlog/log_mapper.cc \
	libzlog/log_mapper.h\
        libzlog/zlog-kv.cc\
        libzlog/zlog-kv.h

libzlog_la_CPPFLAGS = $(BOOST_CPPFLAGS) $(AM_CPPFLAGS)
libzlog_la_LDFLAGS = $(BOOST_SYSTEM_LDFLAGS) $(BOOST_THREAD_LDFLAGS) $(BOOST_PROGRAM_OPTIONS_LDFLAGS)
libzlog_la_LIBADD = $(LIBSEQ) -lcls_zlog_client $(BOOST_SYSTEM_LIBS) $(BOOST_THREAD_LIBS) $(BOOST_PROGRAM_OPTIONS_LIBS)
