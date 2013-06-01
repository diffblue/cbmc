SRC = main.cpp java_bytecode_parse_tree.cpp \
      java_bytecode_typecheck.cpp javap_parse.cpp \
      java_bytecode_convert.cpp java_types.cpp java_entry_point.cpp

OBJ += ../big-int/bigint$(OBJEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../util/util$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../ansi-c/ansi-c$(LIBEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../langapi/langapi$(LIBEXT)

INCLUDES= -I ..

include ../config.inc
include ../common

CLEANFILES = java_bytecode$(LIBEXT)

all: goto-java$(EXEEXT)

###############################################################################

goto-java$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: goto-java-mac-signed

goto-java-mac-signed: goto-cc$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) goto-java$(EXEEXT)

