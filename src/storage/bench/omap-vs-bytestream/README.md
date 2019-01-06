These results are from running the zlog backend benchmark on a cloudlab c220g2
machine with a bluestore OSD on an SSD. The test measured for various log append
sizes the performance when storing the entry data in omap, in the bytestream
(forcing each of those choices), and when using the threshold omap_max_size
parameter set to 4096. The file name format is
"timestamp.entry_size.omap_max_size".
