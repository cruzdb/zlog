noinst_LIBRARIES += libgtest.a
libgtest_a_SOURCES = gtest/src/gtest-all.cc gtest/src/gtest_main.cc
libgtest_a_CPPFLAGS = -Igtest/include -Igtest

GTEST_CXXFLAGS = -I$(top_srcdir)/src/gtest/include
GTEST_LDADD = $(LIBGTEST) -lpthread

bin_PROGRAMS += zlog-test
zlog_test_SOURCES = test/test.cc test/test_internal.cc
zlog_test_CXXFLAGS = $(GTEST_CXXFLAGS)
zlog_test_LDADD = $(LIBZLOG) $(GTEST_LDADD) $(BOOST_SYSTEM_LIBS)

bin_PROGRAMS += zstate-test
zstate_test_SOURCES = test/zstate_test.cc
zstate_test_CXXFLAGS = $(GTEST_CXXFLAGS)
zstate_test_LDADD = $(LIBZLOG) $(LIBZSTATE) $(GTEST_LDADD) $(BOOST_THREAD_LIBS) $(BOOST_SYSTEM_LIBS)
