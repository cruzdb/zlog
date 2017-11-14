pan: pan.c
	$(CC) -Wall -Wno-misleading-indentation -Wno-unused-variable -o $@ $<

pan.c: zlog.pml
	spin -a $<

trail: zlog.pml zlog.pml.trail
	$(HOME)/src/docks/spin/spin -t $<
