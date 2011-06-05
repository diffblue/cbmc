SRC = main.cpp parseoptions.cpp document_claims.cpp languages.cpp \
      uninitialized.cpp uninitialized_domain.cpp full_slicer.cpp \
      object_id.cpp show_locations.cpp points_to.cpp \
      alignment_checks.cpp
OBJ = $(SRC:.cpp=$(OBJEXT)) \
      ../ansi-c/ansi-c$(LIBEXT) \
      ../big-int/bigint$(OBJEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../util/util$(LIBEXT)

INCLUDES= -I .. -I ../util

LIBS =

include ../config.inc
include ../common

all: goto-instrument$(EXEEXT)

ifdef MODULE_CPP
  OBJ += ../cpp/cpp$(LIBEXT)
  CXXFLAGS += -DHAVE_CPP
endif

ifdef MODULE_JAVA
  OBJ += ../java/java$(LIBEXT)
  CXXFLAGS += -DHAVE_JAVA
endif

ifdef MODULE_SPECC
  OBJ += ../specc/specc$(LIBEXT)
  CXXFLAGS += -DHAVE_SPECC
endif

ifdef MODULE_PHP
  OBJ += ../php/php$(LIBEXT)
  CXXFLAGS += -DHAVE_PHP
endif

###############################################################################

goto-instrument$(EXEEXT): $(OBJ)
	$(LINKBIN) $(OBJ)

clean:
	rm -f $(SRC:.cpp=$(OBJEXT)) goto-instrument$(EXEEXT)
