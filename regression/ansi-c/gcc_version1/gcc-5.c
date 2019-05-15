// These types should *not* be provided when emulating gcc-5:
typedef float _Float32;
typedef double _Float32x;
typedef double _Float64;
typedef long double _Float64x;
typedef long double _Float128;
typedef long double _Float128x;

// But this type should:
__float128 f128;
