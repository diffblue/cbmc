// $Id: allocainc.h,v 1.7 2005-12-25 14:44:24 kroening Exp $

// Whatever is necessary to use alloca().

#ifndef ALLOCAINC_H
#define ALLOCAINC_H


#if defined linux || defined __linux__		\
 || defined sun					\
 || defined UWIN				\
 || defined osf1                                \
 || defined __MACH__                            \
 || defined __CYGWIN__

#include <alloca.h>

#elif defined _MSC_VER    \
   || defined __BORLANDC__ \
   || defined __MINGW32__

# include <malloc.h>

#elif defined __vax

// In vax-alloca.mar.
extern "C" void *alloca (unsigned);

#elif defined __VMS

// DEC CXX on VMS alpha.
# include <builtins.h>
# define alloca(N) __ALLOCA(N)

#elif defined __xlC__

# pragma alloca
# include <stdlib.h>

#elif defined __FCC__

# define alloca(X) __builtin_alloca(X)

#elif defined __FreeBSD__

# include <stdlib.h>

#endif


#endif//ndef ALLOCAINC_H
