all: rbt thrash

rbt: rbt.cc kvstore.proto
	protoc -I=. --cpp_out=. kvstore.proto
	g++ -Wall -std=c++11 -o $@ $<
	
thrash: thrash.cc rbt.cc ptree.h
	g++ -Wall -std=c++11 -o $@ $<
