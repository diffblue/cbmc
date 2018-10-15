SRC = converter.cpp \
      # Empty last line

OBJ +=

INCLUDES=

LIBS =

LIBRARY_DIR = ../../../lib/java-models-library

include ../../config.inc
include ../../$(CPROVER_DIR)/src/config.inc
include ../../$(CPROVER_DIR)/src/common

CLEANFILES = converter$(EXEEXT)

all: library converter$(EXEEXT)

clean: clean_library

.PHONY: clean_library
clean_library:
	rm -rf core-models.jar
	if [ -d $(LIBRARY_DIR) ]; then cd $(LIBRARY_DIR); mvn --quiet clean; fi

.PHONY: library
library:
	if [ -d $(LIBRARY_DIR) ]; then \
		(cd $(LIBRARY_DIR); mvn --quiet package); \
		cp $(LIBRARY_DIR)/target/core-models.jar .; \
	fi

###############################################################################

converter$(EXEEXT): $(OBJ)
	$(LINKBIN)
