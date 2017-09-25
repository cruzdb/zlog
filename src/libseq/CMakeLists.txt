add_library(zlog_seqr SHARED libseqr.cc)
target_link_libraries(zlog_seqr
    zlog_proto
    ${Boost_SYSTEM_LIBRARY}
)
install(TARGETS zlog_seqr DESTINATION ${CMAKE_INSTALL_LIBDIR})
