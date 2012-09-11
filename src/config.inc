# Build platform (use one of AUTO, Unix, OSX_Universal, MSVC, Cygwin, MinGW)
BUILD_ENV = AUTO

# Variables you may want to override
#CXXFLAGS = -Wall -O0 -g -Werror -Wno-long-long -Wno-sign-compare -Wno-parentheses -Wno-strict-aliasing -pedantic

# SAT-solvers we have
#PRECOSAT = ../../precosat-576-7e5e66f-120112
#PICOSAT = ../../picosat-936
#LINGELING = ../../lingeling-587f-4882048-110513
#CHAFF = ../../zChaff
#BOOLEFORCE = ../../booleforce-0.4
#MINISAT = ../../MiniSat-p_v1.14
MINISAT2 = ../../../../minisat-2.2.0
#SMVSAT =

# Signing identity for MacOS Gatekeeper

OSX_IDENTITY="3rd Party Mac Developer Application: Daniel Kroening"
