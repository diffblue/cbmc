
CPLUSFLAGS = -g

all: miniBDD.o test_miniBDD

miniBDD.h:
miniBDD.cpp:

miniBDD.o: miniBDD.cpp miniBDD.inc miniBDD.h
	g++ $(CPLUSFLAGS) -c miniBDD.cpp -o miniBDD.o

test_miniBDD.o: miniBDD.inc miniBDD.h test_miniBDD.cpp
	g++ $(CPLUSFLAGS) -c test_miniBDD.cpp -o test_miniBDD.o

test_miniBDD: miniBDD.o test_miniBDD.o
	g++ $(CPLUSFLAGS) miniBDD.o test_miniBDD.o -o test_miniBDD

clean:
	$(RM) miniBDD.o test_miniBDD.o test_miniBDD

miniBDD.tgz: miniBDD.cpp miniBDD.inc miniBDD.h test_miniBDD.cpp Makefile
	tar cvfz miniBDD.tgz miniBDD.cpp miniBDD.inc \
	miniBDD.h test_miniBDD.cpp Makefile
