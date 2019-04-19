#define CONCAT(a, b) a##b
#define CONCAT2(a, b) CONCAT(a, b)

#define STATIC_ASSERT(condition)                                               \
  int CONCAT2(some_array, __LINE__)[(condition) ? 1 : -1]

// hex-based constants
STATIC_ASSERT(0x1.0p-95f == 2.524355e-29f);

// also with upper case X, P, F
STATIC_ASSERT(0X1.0P-95F == 2.524355e-29f);

// nothing before the dot
STATIC_ASSERT(0X.0p+1f == 0);

// 32-bit, 64-bit and 128-bit constants, GCC proper only,
// clang doesn't have it
#if defined(__GNUC__) && !defined(__clang__) && __GNUC__ >= 7
STATIC_ASSERT(__builtin_types_compatible_p(_Float32, __typeof(1.0f32)));
STATIC_ASSERT(__builtin_types_compatible_p(_Float64, __typeof(1.0f64)));
STATIC_ASSERT(__builtin_types_compatible_p(_Float128, __typeof(1.0f128)));
STATIC_ASSERT(__builtin_types_compatible_p(_Float32x, __typeof(1.0f32x)));
STATIC_ASSERT(__builtin_types_compatible_p(_Float64x, __typeof(1.0f64x)));
STATIC_ASSERT(__builtin_types_compatible_p(_Float128x, __typeof(1.0f128x)));
#endif

#ifdef __GNUC__
_Complex c;
#endif

int main()
{
  // imaginary constants, these are GCC only
  #ifdef __GNUC__
  c=(__extension__ 1.0iF);
  c=(__extension__ 1.0Fi);
  c=(__extension__ 1.0jF);
  c=(__extension__ 1.0j);
  c=(__extension__ 1.0jL);
  c=(__extension__ 1.0il);
  #endif
}
