# TODO: this needs Ceph-side support that needs clean-up
# and isn't crucial to zlog. hopefully we can find a way to
# keep it around in some form or another, perhaps in a separate
# Ceph branch.
#bin_PROGRAMS += physical-design
#physical_design_SOURCES = bench/physical-design/physical-design.cc
#physical_design_LDFLAGS = $(BOOST_PROGRAM_OPTIONS_LDFLAGS)
#physical_design_LDADD = $(BOOST_PROGRAM_OPTIONS_LIBS) -lcls_zlog_bench_client

bin_PROGRAMS += zlog-bench
zlog_bench_SOURCES = bench/bench.cc
zlog_bench_LDFLAGS = $(BOOST_PROGRAM_OPTIONS_LDFLAGS)
zlog_bench_LDADD = $(LIBSEQ) $(LIBZLOG) $(BOOST_PROGRAM_OPTIONS_LIBS)
