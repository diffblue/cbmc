# Build platform (use one of AUTO, Unix, OSX_Universal, MSVC, Cygwin, MinGW)
BUILD_ENV = AUTO

# Enable all warnings and treat them as errors
ifeq ($(BUILD_ENV),MSVC)
  #CXXFLAGS += /Wall /WX
else
  CXXFLAGS += -Wall -pedantic -Werror
endif

# Select optimisation or debug info
#CXXFLAGS += -O2 -DNDEBUG
#CXXFLAGS += -O0 -g

ifeq ($(shell uname),Linux)
  CXXFLAGS += -DUSE_BOOST
endif

ifeq ($(BUILD_ENV),MSVC)
  LIBS=shlwapi.lib
endif

# If GLPK is available; this is used by goto-instrument and musketeer.
#LIB_GLPK = -lglpk

# SAT-solvers we have
#PRECOSAT = ../../precosat-576-7e5e66f-120112
#PICOSAT = ../../picosat-959
#LINGELING = ../../lingeling-587f-4882048-110513
#CHAFF = ../../zChaff
#BOOLEFORCE = ../../booleforce-0.4
#MINISAT = ../../MiniSat-p_v1.14
MINISAT2 = ../../minisat-2.2.1
#GLUCOSE = ../../glucose-syrup
#SMVSAT =

ifneq ($(PRECOSAT),)
  CP_CXXFLAGS += -DSATCHECK_PRECOSAT
endif

ifneq ($(PICOSAT),)
  CP_CXXFLAGS += -DSATCHECK_PICOSAT
endif

ifneq ($(LINGELING),)
  CP_CXXFLAGS += -DSATCHECK_LINGELING
endif

ifneq ($(CHAFF),)
  CP_CXXFLAGS += -DSATCHECK_CHAFF
endif

ifneq ($(BOOLEFORCE),)
  CP_CXXFLAGS += -DSATCHECK_BOOLEFORCE
endif

ifneq ($(MINISAT),)
  CP_CXXFLAGS += -DSATCHECK_MINISAT
endif

ifneq ($(MINISAT2),)
  CP_CXXFLAGS += -DSATCHECK_MINISAT2
endif

ifneq ($(GLUCOSE),)
  CP_CXXFLAGS += -DSATCHECK_GLUCOSE
endif

ifneq ($(SMVSAT),)
  CP_CXXFLAGS += -DSATCHECK_SMVSAT
endif

# Signing identity for MacOS Gatekeeper

OSX_IDENTITY="Developer ID Application: Daniel Kroening"
