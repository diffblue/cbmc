# Build platform (use one of AUTO, Unix, OSX_Universal, MSVC, Cygwin, MinGW)
BUILD_ENV = AUTO

# Enable all warnings
#CXXFLAGS += -Wall -Wno-long-long -Wno-sign-compare -Wno-parentheses -Wno-strict-aliasing -pedantic

# Treat warnings as errors
#CXXFLAGS += -Werror

# Select optimisation or debug info
#CXXFLAGS += -O2 -DNDEBUG
#CXXFLAGS += -O0 -g

CXXFLAGS += -DUSE_BOOST
LIBS=-lboost_filesystem -lboost_system

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
LIBZIPLIB = ../../libzip/lib/.libs/libzip.a ../../zlib/libz.a
LIBZIPINC = ../../libzip/lib

# Signing identity for MacOS Gatekeeper

OSX_IDENTITY="Developer ID Application: Daniel Kroening"
