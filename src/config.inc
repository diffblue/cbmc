# Build platform (use one of AUTO, Unix, OSX_Universal, MSVC, Cygwin, MinGW)
BUILD_ENV = AUTO

# Enable all warnings and treat them as errors
ifeq ($(BUILD_ENV),MSVC)
  CXXFLAGS += /Wall /WX
  # disable warning "decorated name length exceeded"
  CXXFLAGS += /wd4503
  # disable deprecation warnings
  CXXFLAGS += /wd4996
  # disable warning "unreferenced inline function has been removed"
  CXXFLAGS += /wd4514
  # disable warning "padding added after data member"
  CXXFLAGS += /wd4820
  # disable warning "function not inlined"
  CXXFLAGS += /wd4710
  # disable warning "layout of class may have changed from a previous version of
  # the compiler due to better packing of member"
  CXXFLAGS += /wd4371 /wd4435
  # disable warning "conditional expression is constant"
  CXXFLAGS += /wd4127
  # disable warning "behavior change ... called instead of ..."
  CXXFLAGS += /wd4350
  # disable warning "assignment operator could not be generated"
  CXXFLAGS += /wd4512 /wd4626
  # disable warning "default/copy constructor could not be generated"
  CXXFLAGS += /wd4623 /wd4510 /wd4625 /wd4610
  # disable warning "no override available, function is hidden"
  CXXFLAGS += /wd4266
  # disable warning "unreferenced local function has been removed"
  CXXFLAGS += /wd4505
  # disable warning "'this' used in base member initializer list" - which would
  # be useful to have, but it's not always clear where to put a silencing pragma
  CXXFLAGS += /wd4355
  # disable warning "#pragma warning(pop): likely mismatch, popping warning
  # state pushed in different file"
  CXXFLAGS += /wd5031 /wd5032
  # disable warning "move constructor/assignment operator was implicitly defined
  # as deleted"
  CXXFLAGS += /wd5026 /wd5027
  # disable warning "Informational: catch(...) semantics changed since Visual
  # C++ 7.1; structured exceptions (SEH) are no longer caught"
  CXXFLAGS += /wd4571
  # disable warning "Compiler will insert Spectre mitigation with /Qspectre"
  CXXFLAGS += /wd5045
  # disable warning "signed/unsigned mismatch" as VS2017 STL headers yield it
  # CXXFLAGS += /wd4365
  # disable warning "format string expected is not a string literal" as VS2017 STL headers yield it
  CXXFLAGS += /wd4774
  # disable warning "#pragma warning: there is no warning number '...'" to
  # support multiple Visual Studio versions
  CXXFLAGS += /wd4619
else
  CXXFLAGS += -Wall -pedantic -Werror -Wno-deprecated-declarations -Wswitch-enum
endif

# Select optimisation or debug info
#CXXFLAGS += -O2 -DNDEBUG
#CXXFLAGS += -O0 -g

# With GCC this adds function names in stack backtraces
#LINKFLAGS="-rdynamic"

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
CBMC_VERSION = 5.11
