all: rbt thrash db_test

kvstore.pb.o: kvstore.proto
	protoc -I=. --cpp_out=. kvstore.proto
	g++ -g -Wall -c -o kvstore.pb.o kvstore.pb.cc

transaction.o: transaction.cc transaction.h
	g++ -g -Wall -std=c++11 -c -o $@ $<

db.o: db.cc db.h kvstore.pb.o
	g++ -g -Wall -c -o $@ $<

rbt: rbt.cc db.o kvstore.pb.o transaction.o
	g++ -g -Wall -std=c++11 -o $@ db.o transaction.o kvstore.pb.o $< -lprotobuf -lpthread
	
thrash: thrash.cc db.o kvstore.pb.o transaction.o
	g++ -g -Wall -std=c++11 -o $@ db.o transaction.o kvstore.pb.o $< -lprotobuf -lpthread

db_test: db_test.cc db.o kvstore.pb.o transaction.o
	g++ -g -Wall -std=c++11 -o $@ db.o transaction.o kvstore.pb.o $< -lprotobuf -lpthread

clean:
	rm -f rbt db_test thrash kvstore.pb.h kvstore.pb.cc kvstore.pb.o
