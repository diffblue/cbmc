.PHONY: all cprover.dir test

SRC = unit_tests.cpp \
      catch_example.cpp \
      analyses/variable-sensitivity/abstract_object/merge.cpp \
      # Empty last line

INCLUDES= -I ../src/ -I.

include ../src/config.inc
include ../src/common

cprover.dir:
	$(MAKE) $(MAKEARGS) -C ../src

LIBS = ../src/ansi-c/ansi-c$(LIBEXT) \
       ../src/cpp/cpp$(LIBEXT) \
       ../src/json/json$(LIBEXT) \
       ../src/linking/linking$(LIBEXT) \
       ../src/util/util$(LIBEXT) \
       ../src/big-int/big-int$(LIBEXT) \
       ../src/goto-programs/goto-programs$(LIBEXT) \
       ../src/pointer-analysis/pointer-analysis$(LIBEXT) \
       ../src/langapi/langapi$(LIBEXT) \
       ../src/assembler/assembler$(LIBEXT) \
       ../src/analyses/analyses$(LIBEXT) \
       ../src/solvers/solvers$(LIBEXT) \
       # Empty last line

TESTS = unit_tests$(EXEEXT) \
        miniBDD$(EXEEXT) \
        string_utils$(EXEEXT) \
        sharing_node$(EXEEXT) \
        # Empty last line

CLEANFILES = $(TESTS)

all: cprover.dir
	$(MAKE) $(MAKEARGS) $(TESTS)

test: all
	$(foreach test,$(TESTS), (echo Running: $(test); ./$(test)) &&) true


###############################################################################

unit_tests$(EXEEXT): $(OBJ)
	$(LINKBIN)

miniBDD$(EXEEXT): miniBDD$(OBJEXT)
	$(LINKBIN)

string_utils$(EXEEXT): string_utils$(OBJEXT)
	$(LINKBIN)

sharing_node$(EXEEXT): sharing_node$(OBJEXT)
	$(LINKBIN)
