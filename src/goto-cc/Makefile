SRC = goto-cc.cpp \
      cmdline_options.cpp get_base_name.cpp \
      gcc_cmdline.cpp ms_cl_cmdline.cpp \
      compile.cpp armcc_cmdline.cpp \
      languages.cpp goto_cc_cmdline.cpp \
      xml_binaries/xml_irep_hashing.cpp \
      xml_binaries/xml_symbol_hashing.cpp \
      xml_binaries/xml_symbol.cpp \
      xml_binaries/xml_goto_function.cpp \
      xml_binaries/xml_goto_function_hashing.cpp \
      xml_binaries/xml_goto_program.cpp \
      xml_binaries/xml_goto_program_hashing.cpp \
      xml_binaries/read_goto_object.cpp

OBJ = $(SRC:.cpp=$(OBJEXT)) \
      ../big-int/bigint$(OBJEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../ansi-c/ansi-c$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../langapi/langapi$(LIBEXT)

INCLUDES= -I .. -I ../util

LIBS =

include ../config.inc
include ../common

all: goto-cc$(EXEEXT)

ifdef MODULE_CPP
  OBJ += ../cpp/cpp$(LIBEXT)
  CXXFLAGS += -D HAVE_CPP
endif

###############################################################################

goto-cc$(EXEEXT): $(OBJ)
	$(LINKBIN) $(OBJ)

clean:
	rm -f $(SRC:.cpp=$(OBJEXT)) $(SRC:.cpp=.d) goto-cc$(EXEEXT)
