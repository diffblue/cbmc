// All these types should be provided when emulating gcc-7:

#ifndef __clang__
_Float32 f32;
_Float32x f32x;
_Float64 f64;
_Float64x f64x;
_Float128 f128;
_Float128x f128x;

// https://gcc.gnu.org/onlinedocs/gcc/Floating-Types.html
#  if defined(__i386__) || defined(__x86_64__) || defined(__ia64__) ||         \
    defined(__hppa__) || defined(__powerpc__)
__float128 gcc_f128;
#endif
#endif
