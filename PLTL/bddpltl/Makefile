
OBJS=bddpltl.o PLTLFormula.o PLTLMisc.o
DEBUG_OBJS=$(patsubst %.o,%.d.o,$(OBJS))

CFLAGS= -g -Wall -Wextra -Weffc++ --std=c++0x
OPTFLAGS= -O2

all: bddpltl

bddpltl: $(OBJS)
	g++ $(CFLAGS) $(OPTFLAGS) -o bddpltl $(OBJS) -lbdd

debug: $(DEBUG_OBJS)
	g++ $(CFLAGS) -O0 -o bddpltl.d $(DEBUG_OBJS) -lbdd #-L../buddy/ -lmybdd

%.cpp: %.h

%.d.o: %.cpp
	g++ $(CFLAGS) -O0 -o $@ -c $<

%.o: %.cpp
	g++ $(CFLAGS) $(OPTFLAGS) -c $<

.PHONY: clean
clean:
	-rm *.o *~

.PHONY: distclean
distclean: clean
	- rm bddpltl bddpltl.d
