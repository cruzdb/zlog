import sys
import pandas as pd
import matplotlib
import matplotlib.pyplot as plt

matplotlib.style.use('ggplot')

with open(sys.argv[1]) as f:
    table = pd.read_table(f, sep=" ", header=None,
        names=("start", "latency"))

# use zero start time in seconds
table['start'] = table['start'] - min(table['start'])
table['start'] = table['start'] / (10.0**9)

# convert from ns to ms
table['latency'] = table['latency'] / (10.0**6)

ax = table.plot(x='start', y='latency')
ax.set_xlabel("time (sec)")
ax.set_ylabel("latency (ms)")

plt.show()
