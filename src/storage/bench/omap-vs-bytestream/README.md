These results are from running the zlog backend benchmark on a cloudlab c220g2
machine with a bluestore OSD on an SSD. The test measured for various log append
sizes the performance when storing the entry data in omap or in the bytestream.
The code to make this work was a hack (hole punch down into the ceph backend),
and there is a patch here that would work as guidance to reproduce the same
feature.
