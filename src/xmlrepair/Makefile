SRC = xmlrepair.cpp ../util/unicode.cpp

OBJ += 

INCLUDES= -I ..

LIBS =

CLEANFILES = xmlrepair$(EXEEXT)

include ../config.inc
include ../common

all: xmlrepair$(EXEEXT)

###############################################################################

xmlrepair$(EXEEXT): $(OBJ)
	$(LINKBIN)

.PHONY: xmlrepair-mac-signed

xmlrepair-mac-signed: xmlrepair$(EXEEXT)
	codesign -v -s $(OSX_IDENTITY) xmlrepair$(EXEEXT)

