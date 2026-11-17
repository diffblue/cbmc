// A <math.h> that defines signbit by a function of the C library that the
// CPROVER library does not model, as some C libraries do (OpenBSD's uses
// __signbit, __signbitf and __signbitl)
#include_next <math.h>
#undef signbit
int unmodelled_signbit(double);
#define signbit(x) unmodelled_signbit(x)
