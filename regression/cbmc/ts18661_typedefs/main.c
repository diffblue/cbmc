#if defined(__GNUC__) && !defined(__clang__)

#include <features.h> // For __GNUC_PREREQ

#ifdef __x86_64__
#define FLOAT128_MINOR_VERSION 3
#else
#define FLOAT128_MINOR_VERSION 5
#endif

#if __GNUC__ >= 7
#define HAS_FLOATN
#elif __GNUC_PREREQ(4, FLOAT128_MINOR_VERSION)
#define HAS_FLOAT128
#endif

#endif

#ifndef HAS_FLOATN
typedef float _Float32;
typedef double _Float32x;
typedef double _Float64;
typedef long double _Float64x;
typedef long double _Float128x;
#endif

#if !defined(HAS_FLOATN) && !defined(HAS_FLOAT128)
typedef long double _Float128;
#endif

int main(int argc, char** argv) {
}
