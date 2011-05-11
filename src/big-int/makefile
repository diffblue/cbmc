RM = rm -f

include ../config.inc
include ../common

OBJ = bigint-test$(OBJEXT) bigint-func$(OBJEXT) bigint$(OBJEXT)
PRG = test-bigint$(EXEEXT)

all : $(PRG)

clean :
	$(RM) $(OBJ) $(PRG)

.cc$(OBJEXT):
	$(CXX) -c $(CXXFLAGS) -o $@ $<

$(PRG): $(OBJ)
	$(CXX) $(CXXFLAGS) -o $(PRG) $(OBJ)

dep:
