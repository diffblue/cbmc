CC     = gcc
CXX    = g++
LD     = ld
AR     = ar
YACC   = bison -y
YFLAGS = -v
LEX    = flex
#CC     = icc
#CXX    = icpc

# Linux etc.
LIBEXT = .a
OBJEXT = .o
EXEEXT =
GCCFLAGS = -Wall -MMD -O2
#LINKFLAGS = -static
LINKLIB = ld -r -o $@ $^
LINKBIN = $(CXX) $(LINKFLAGS) -o $@ $(LIBS)

# MacOS Fat Binaries
# LIBEXT = .a
# OBJEXT = .o
# EXEEXT =
# GCCFLAGS = -Wall -MMD -O2 -force_cpusubtype_ALL -arch i386 -arch ppc -arch x86_64
# LINKFLAGS = -force_cpusubtype_ALL -arch i386 -arch ppc -arch x86_64
# LINKLIB = ld -r -o $@ $^
# LINKBIN = $(CXX) $(LINKFLAGS) -o $@ $(LIBS)

# use these for Cygwin/MingW32:
# LIBEXT = .a
# OBJEXT = .o
# EXEEXT =
# GCCFLAGS = -Wall -MMD -O2 -mno-cygwin
# LINKFLAGS = -static
# LINKLIB = ld -r -o $@ $^
# LINKBIN = $(CXX) $(LINKFLAGS) -o $@ $(LIBS)
# CC = i686-pc-mingw32-gcc
# CXX = i686-pc-mingw32-g++

# use these for Visual Studio:
# LIBEXT = .lib
# OBJEXT = .obj
# EXEEXT = .exe
# CXX = cl
# CC = cl
# LINKLIB = lib /NOLOGO /OUT:$@ $^
# LINKBIN = $(CXX) $(LINKFLAGS) /Fe$@ $(LIBS)

# SAT-solvers we have
#CHAFF = ../../zChaff
#BOOLEFORCE = ../../booleforce-0.4
#MINISAT = ../../MiniSat-p_v1.14
MINISAT2 = ../../../../minisat-2.2.0
#SMVSAT =

LANGUAGES = ansi-c csp intrep pvs smvlang verilog vhdl netlist cpp specc \
            xmllang promela pascal bplang csharp smtlang nsf mdllang java

# modules that we have
#MODULE_PROVER = 1
#MODULE_IPP = 1
#MODULE_INTERPOLATION = 1
#MODULE_BV_REFINEMENT = 1
#MODULE_SATQE = 1
MODULE_CPP = 1
#MODULE_SMTLANG = 1
#MODULE_SPECC = 1
MODULE_VERILOG = 1
#MODULE_VHDL = 1
#MODULE_PASCAL = 1
#MODULE_PHP = 1
#MODULE_SIMPLIFYLANG = 1
#MODULE_HW_CBMC = 1
#MODULE_CEMC = 1
MODULE_FLOATBV = 1
#MODULE_SMV = 1
