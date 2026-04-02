// _Float16 requires GCC >= 12 or Clang >= 15.
// On other compilers, fall back to a trivial float test.
#if defined(__GNUC__) && !defined(__clang__) && __GNUC__ >= 12
#  define HAS_FLOAT16
#elif defined(__clang__) && __clang_major__ >= 15
#  define HAS_FLOAT16
#endif

#ifdef HAS_FLOAT16

int main()
{
  _Float16 a = 3.0f16;
  _Float16 b = 2.0f16;

  __CPROVER_assert(a + b == 5.0f16, "add");
  __CPROVER_assert(a - b == 1.0f16, "sub");
  __CPROVER_assert(a * b == 6.0f16, "mul");
  __CPROVER_assert(a / b == 1.5f16, "div");
  __CPROVER_assert(a > b, "gt");
  __CPROVER_assert(b < a, "lt");
  __CPROVER_assert(-a == -3.0f16, "neg");

  int i = (int)a;
  __CPROVER_assert(i == 3, "to_int");
  _Float16 c = (_Float16)5;
  __CPROVER_assert(c == 5.0f16, "from_int");
  float d = (float)a;
  __CPROVER_assert(d == 3.0f, "f16_to_f32");
}

#else

int main()
{
}

#endif
