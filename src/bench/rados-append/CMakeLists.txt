add_executable(rados_append_bench rados-append.cc)
target_link_libraries(rados_append_bench
  rados
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  ${Boost_SYSTEM_LIBRARY}
  atomic
  hdr_histogram_static
  pthread
)
install(TARGETS rados_append_bench DESTINATION bin)
