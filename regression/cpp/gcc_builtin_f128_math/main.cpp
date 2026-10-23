// GCC _Float128 math builtins used by libstdc++ headers

#if defined(__GNUC__) && !defined(__clang__) && defined(__x86_64__)

__float128 x = 1.0;

__float128 test_fabs()
{
  return __builtin_fabsf128(x);
}

__float128 test_sqrt()
{
  return __builtin_sqrtf128(x);
}

__float128 test_copysign()
{
  return __builtin_copysignf128(x, x);
}

#endif

int main()
{
  return 0;
}
