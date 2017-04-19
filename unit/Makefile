SRC = cpp_parser.cpp \
      cpp_scanner.cpp \
      elf_reader.cpp \
      float_utils.cpp \
      ieee_float.cpp \
      json.cpp \
      miniBDD.cpp \
      osx_fat_reader.cpp \
      sharing_map.cpp \
      sharing_node.cpp \
      smt2_parser.cpp \
      string_utils.cpp \
      wp.cpp \
      # Empty last line

INCLUDES= -I ../src/

include ../src/config.inc
include ../src/common

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

CLEANFILES = $(SRC:.cpp=$(EXEEXT))

all: $(SRC:.cpp=$(EXEEXT))

###############################################################################

cpp_parser$(EXEEXT): cpp_parser$(OBJEXT)
	$(LINKBIN)

cpp_scanner$(EXEEXT): cpp_scanner$(OBJEXT)
	$(LINKBIN)

elf_reader$(EXEEXT): elf_reader$(OBJEXT)
	$(LINKBIN)

float_utils$(EXEEXT): float_utils$(OBJEXT)
	$(LINKBIN)

ieee_float$(EXEEXT): ieee_float$(OBJEXT)
	$(LINKBIN)

json$(EXEEXT): json$(OBJEXT)
	$(LINKBIN)

miniBDD$(EXEEXT): miniBDD$(OBJEXT)
	$(LINKBIN)

osx_fat_reader$(EXEEXT): osx_fat_reader$(OBJEXT)
	$(LINKBIN)

smt2_parser$(EXEEXT): smt2_parser$(OBJEXT)
	$(LINKBIN)

wp$(EXEEXT): wp$(OBJEXT)
	$(LINKBIN)

string_utils$(EXEEXT): string_utils$(OBJEXT)
	$(LINKBIN)

sharing_map$(EXEEXT): sharing_map$(OBJEXT)
	$(LINKBIN)

sharing_node$(EXEEXT): sharing_node$(OBJEXT)
	$(LINKBIN)

