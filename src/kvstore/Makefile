all: rbt thrash

kvstore.pb.o: kvstore.proto
	protoc -I=. --cpp_out=. kvstore.proto
	g++ -g -Wall -c -o kvstore.pb.o kvstore.pb.cc

rbt: rbt.cc kvstore.pb.o
	g++ -g -Wall -std=c++11 -o $@ kvstore.pb.o $< -lprotobuf
	
thrash: thrash.cc rbt.cc ptree.h kvstore.pb.o
	g++ -g -Wall -std=c++11 -o $@ kvstore.pb.o $< -lprotobuf

clean:
	rm -f rbt thrash kvstore.pb.h kvstore.pb.cc kvstore.pb.o
