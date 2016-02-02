lib_LTLIBRARIES += libzlog.la

libzlog_la_SOURCES = \
	libzlog/log_impl.cc \
	libzlog/stream.cc \
	libzlog/aio.cc \
	libzlog/libzlog.hpp \
	libzlog/libzlog.h \
	libzlog/stripe_history.cc \
	libzlog/stripe_history.h \
	libzlog/log_mapper.cc \
	libzlog/log_mapper.h

libzlog_la_CPPFLAGS = $(BOOST_CPPFLAGS)
libzlog_la_LDFLAGS = $(BOOST_SYSTEM_LDFLAGS)
libzlog_la_LIBADD = $(LIBSEQ) -lcls_zlog_client $(BOOST_SYSTEM_LIBS)

include_HEADERS += \
	libzlog/libzlog.h \
	libzlog/libzlog.hpp
