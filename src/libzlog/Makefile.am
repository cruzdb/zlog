lib_LTLIBRARIES += libzlog.la

libzlog_la_SOURCES = \
	libzlog/libzlog.cc \
	libzlog/stream.cc \
	libzlog/aio.cc \
	libzlog/libzlog.hpp \
	libzlog/libzlog.h \
	libzlog/stripe_history.cc \
	libzlog/stripe_history.h \
	libzlog/log_mapper.cc \
	libzlog/log_mapper.h

libzlog_la_CPPFLAGS = $(BOOST_CPPFLAGS) -DBOOST_LOG_DYN_LINK
libzlog_la_LDFLAGS = $(BOOST_SYSTEM_LDFLAGS) $(BOOST_LOG_LDFLAGS)
libzlog_la_LIBADD = $(LIBSEQ) -lcls_zlog_client $(BOOST_SYSTEM_LIBS) $(BOOST_LOG_LIBS)

include_HEADERS += \
	libzlog/libzlog.h \
	libzlog/libzlog.hpp
