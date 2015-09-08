AC_PREREQ(2.59)

AC_INIT([zlog], [0.1.0], [noahwatkins@gmail.com])

AM_PROG_AR
AC_PROG_LIBTOOL
AC_PROG_CXX
AC_LANG([C++])

AC_CONFIG_MACRO_DIR([m4])

AM_INIT_AUTOMAKE([-Wall -Werror foreign subdir-objects])

m4_ifdef([AM_SILENT_RULES], [AM_SILENT_RULES([yes])])

AX_CXX_COMPILE_STDCXX_11([],[mandatory])

BOOST_REQUIRE([1.46])
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

AC_LANG([C++])
SAVED_LDFLAGS=$LDFLAGS
LDFLAGS="$LDFLAGS -lcls_zlog_client"
AC_LINK_IFELSE([
  AC_LANG_PROGRAM(
    [#include <rados/cls_zlog_client.h>],
    [void (*p)(librados::ObjectWriteOperation&, uint64_t); p = zlog::cls_zlog_seal;])
  ], [], [AC_MSG_FAILURE([libcls_zlog_client not found])]) 
LDFLAGS=$SAVED_LDFLAGS

AC_CONFIG_FILES([
  Makefile
  src/Makefile
])

AC_OUTPUT
