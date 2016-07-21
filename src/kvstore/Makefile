all: rbt thrash db_test

kvstore.pb.o: kvstore.proto
	protoc -I=. --cpp_out=. kvstore.proto
	g++ -g -Wall -c -o kvstore.pb.o kvstore.pb.cc

db.o: db.cc db.h kvstore.pb.o
	g++ -g -Wall -c -o $@ $<

rbt: rbt.cc db.o kvstore.pb.o
	g++ -g -Wall -std=c++11 -o $@ db.o kvstore.pb.o $< -lprotobuf
	
thrash: thrash.cc db.o kvstore.pb.o
	g++ -g -Wall -std=c++11 -o $@ db.o kvstore.pb.o $< -lprotobuf

db_test: db_test.cc db.o kvstore.pb.o
	g++ -g -Wall -std=c++11 -o $@ db.o kvstore.pb.o $< -lprotobuf

clean:
	rm -f rbt db_test thrash kvstore.pb.h kvstore.pb.cc kvstore.pb.o
