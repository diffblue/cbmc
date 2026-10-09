// _Float32/64/32x/64x are GCC 13+ built-in types in C++ mode.
#if defined(__GNUC__) && !defined(__clang__) && __GNUC__ >= 13
_Float32 f32 = 1.0f;
_Float64 f64 = 2.0;
_Float32x f32x = 3.0;
_Float64x f64x = 4.0;
#endif

int main()
{
  return 0;
}
