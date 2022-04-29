# Build platform (use one of AUTO, Unix, OSX_Universal, MSVC, Cygwin, MinGW)
BUILD_ENV = AUTO

# Enable all warnings and treat them as errors
ifeq ($(BUILD_ENV),MSVC)
  #CXXFLAGS += /Wall /WX
else
  CXXFLAGS += -Wall -pedantic -Werror -Wno-deprecated-declarations -Wswitch-enum
endif

ifeq ($(CPROVER_WITH_PROFILING),1)
  CXXFLAGS += -fprofile-arcs -ftest-coverage
  LINKFLAGS += -lgcov -fprofile-arcs
endif

# Select optimisation or debug info
#CXXFLAGS += -O2 -DNDEBUG
#CXXFLAGS += -O0 -g

# With GCC this adds function names in stack backtraces
#LINKFLAGS = -rdynamic

# If GLPK is available; this is used by goto-instrument and musketeer.
#LIB_GLPK = -lglpk

# SAT-solvers we have
#PICOSAT = ../../picosat-959
#LINGELING = ../../lingeling-587f-4882048-110513
#CHAFF = ../../zChaff
#BOOLEFORCE = ../../booleforce-0.4
#MINISAT = ../../MiniSat-p_v1.14
#MINISAT2 = ../../minisat-2.2.1
#IPASIR = ../../ipasir
#GLUCOSE = ../../glucose-syrup
#CADICAL = ../../cadical

# select default solver to be minisat2 if no other is specified
ifeq ($(BOOLEFORCE)$(CHAFF)$(GLUCOSE)$(IPASIR)$(LINGELING)$(MINISAT)$(MINISAT2)$(PICOSAT)$(CADICAL),)
  MINISAT2 = ../../minisat-2.2.1
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

ifneq ($(CADICAL),)
  CP_CXXFLAGS += -DSATCHECK_CADICAL
endif

# Signing identity for MacOS Gatekeeper

OSX_IDENTITY="Developer ID Application: Daniel Kroening"

# Detailed version information
CBMC_VERSION = 5.56.0

# Use the CUDD library for BDDs, can be installed using `make -C src cudd-download`
# CUDD = ../../cudd-3.0.0
