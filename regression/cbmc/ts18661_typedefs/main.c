#if defined(__clang__)
#elif defined(__GNUC__)
#if __GNUC__ >= 7
#define HAS_FLOATN
#endif
#endif

#ifndef HAS_FLOATN
typedef float _Float32;
typedef double _Float32x;
typedef double _Float64;
typedef long double _Float64x;
typedef long double _Float128;
typedef long double _Float128x;
#endif

int main(int argc, char** argv) {
}
