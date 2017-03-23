SRC = clobber_main.cpp \
      clobber_parse_options.cpp \
      # Empty last line

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
       ../cpp/cpp$(LIBEXT) \
       ../linking/linking$(LIBEXT) \
       ../big-int/big-int$(LIBEXT) \
       ../goto-programs/goto-programs$(LIBEXT) \
       ../analyses/analyses$(LIBEXT) \
       ../langapi/langapi$(LIBEXT) \
       ../xmllang/xmllang$(LIBEXT) \
       ../assembler/assembler$(LIBEXT) \
       ../solvers/solvers$(LIBEXT) \
       ../util/util$(LIBEXT) \
       ../goto-symex/rewrite_union$(OBJEXT) \
       ../pointer-analysis/dereference$(OBJEXT) \
       ../goto-instrument/dump_c$(OBJEXT) \
       ../goto-instrument/goto_program2code$(OBJEXT) \
       # Empty last line

INCLUDES= -I ..

LIBS =

include ../config.inc
include ../common

CLEANFILES = clobber$(EXEEXT)

all: clobber$(EXEEXT)

###############################################################################

clobber$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: clobber-mac-signed

clobber-mac-signed: cbmc$(EXEEXT)
	strip clobber$(EXEEXT) ; codesign -v -s $(OSX_IDENTITY) clobber$(EXEEXT)
