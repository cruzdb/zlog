AC_PREREQ(2.59)

AC_INIT([zlog], [0.0.1], [noahwatkins@gmail.com])

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

AC_CONFIG_FILES([
  Makefile
  src/Makefile
])

AC_OUTPUT
