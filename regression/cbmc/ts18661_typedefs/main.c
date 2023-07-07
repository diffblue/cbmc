#if defined(__GNUC__)

#  ifdef __clang__

#    define HAS_FLOAT128

#  else

#    include <features.h> // For __GNUC_PREREQ

#    ifdef __x86_64__
#      define FLOAT128_MINOR_VERSION 3
#    else
#      define FLOAT128_MINOR_VERSION 5
#    endif

#    if __GNUC__ >= 7
#      define HAS_FLOATN
#    endif

#    if __GNUC_PREREQ(4, FLOAT128_MINOR_VERSION)
// https://gcc.gnu.org/onlinedocs/gcc/Floating-Types.html
#      if defined(__i386__) || defined(__x86_64__) || defined(__ia64__) ||     \
        defined(__hppa__) || defined(__powerpc__)
#        define HAS_FLOAT128
#      endif
#    endif

#  endif

#endif

#ifdef HAS_FLOATN
typedef _Float32 f1;
typedef _Float32x f2;
typedef _Float64 f3;
typedef _Float64x f4;
typedef _Float128 f5;
typedef _Float128x f6;
#else
typedef float _Float32;
typedef double _Float32x;
typedef double _Float64;
typedef long double _Float64x;
typedef long double _Float128;
typedef long double _Float128x;
#endif

#if defined(HAS_FLOAT128)
typedef __float128 f7;
#else
typedef long double __float128;
#endif

int main(int argc, char** argv) {
}
