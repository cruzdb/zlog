import glob

def get_time_bounds(filename):
    start_rt_ns = None
    start_mo_ns = None
    latencies = []
    ts_min, ts_max = None, None
    with open(filename) as f:
        for line in f.readlines():
            parts = line.split(" ")
            if len(parts) == 2:
                startns = long(parts[0])
                latns = long(parts[1])
                assert start_rt_ns
                assert start_mo_ns
                startns_rt = start_rt_ns + (startns - start_mo_ns)
                if ts_min == None:
                    ts_min = startns_rt
                    ts_max = startns_rt
                ts_min = min(ts_min, startns_rt)
                ts_max = max(ts_max, startns_rt)
                latencies.append((startns_rt, latns))
            elif len(parts) == 3 and parts[0] == "init:":
                start_rt_ns = long(parts[1])
                start_mo_ns = long(parts[2])
            else:
                assert False
    return ts_min, ts_max, latencies


mins = []
maxs = []
latency = []

for filename in glob.glob("*.txt"):
    prefix = filename.split(".")[0]
    tsmin, tsmax, latencies = get_time_bounds(filename)
    mins.append(tsmin)
    maxs.append(tsmax)
    latency.append(latencies)

# figure out clipping boundaries. we want the latest start time (which would
# include all workload threads running), and the earliest end time (which
# would include all the workload thread running).
ts_min = max(mins)
ts_max = min(maxs)

all_latency = []
for lats in latency:
    lats = filter(lambda (ts,ns): ts_min < ts and ts < ts_max, lats)
    lats = map(lambda (ts,ns): ns, lats)
    all_latency += lats

diff_ns = ts_max - ts_min
tp = (len(all_latency) * 1000000000) / (ts_max - ts_min)

print "throughput:", tp
print "min:", min(all_latency)*1.0/1000000.0
print "max:", max(all_latency)*1.0/1000000.0
print "avg:", (sum(all_latency)*1.0/len(all_latency))/1000000.0
