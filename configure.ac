AC_PREREQ(2.59)

AC_INIT([zlog], [0.0.1], [noahwatkins@gmail.com])

AM_PROG_AR
AC_PROG_LIBTOOL
AC_PROG_CXX
AC_LANG([C++])

AC_CONFIG_MACRO_DIR([m4])

AM_INIT_AUTOMAKE([-Wall -Werror foreign subdir-objects])

m4_ifdef([AM_SILENT_RULES], [AM_SILENT_RULES([yes])])

BOOST_REQUIRE([1.48])
BOOST_ASIO
BOOST_BIND
BOOST_SYSTEM
BOOST_PROGRAM_OPTIONS

PKG_CHECK_MODULES(PROTOBUF, protobuf >= 2.4.0)
AC_SUBST(PROTOBUF_LIBS)
AC_SUBST(PROTOBUF_CFLAGS)
AC_SUBST(PROTOBUF_VERSION)

AC_CHECK_PROG([PROTOC], [protoc], [protoc])
AS_IF([test "x${PROTOC}" == "x"],
  [AC_MSG_ERROR([ProtoBuf compiler "protoc" not found.])])

AC_CHECK_LIB([rados], [rados_version],, [AC_MSG_FAILURE([librados not found])])
AC_CHECK_HEADER([rados/librados.hpp],, [AC_MSG_FAILURE([librados.hpp not found])])

AC_CHECK_HEADER([glog/logging.h],, [AC_MSG_FAILURE([glog/logging.h not found])])
AC_CHECK_LIB([glog], [_ZN6google10LogMessage4FailEv],, [AC_MSG_FAILURE([libglog not found])])

AC_CONFIG_FILES([
  Makefile
  src/Makefile
])

AC_OUTPUT
