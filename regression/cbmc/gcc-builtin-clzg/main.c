// GCC 14's type-generic bit builtins (GCC reference, "Other Built-in
// Functions"): `int __builtin_clzg(T arg [, int value])' and __builtin_ctzg
// for any unsigned integer type T, the optional second argument being the
// result for arg == 0.  libstdc++ 14+ implements std::countl_zero,
// std::countr_zero and std::bit_width on them.  Both were declared as
// `int f(int)', so the two-argument form was rejected ("wrong number of
// function arguments", C; "found no match", C++) and a wide operand was
// narrowed.
void __CPROVER_assert(_Bool, const char *);
int main()
{
  unsigned a = 1u << 20;
  unsigned long b = 1ul << 40;
  unsigned __int128 c = ((unsigned __int128)1) << 100;
  __CPROVER_assert(__builtin_clz(a) == 11, "clz");
  __CPROVER_assert(__builtin_clzg(a) == 11, "clzg unsigned");
  __CPROVER_assert(__builtin_clzg(b) == 23, "clzg unsigned long");
  __CPROVER_assert(__builtin_clzg(c) == 27, "clzg unsigned __int128");
  __CPROVER_assert(__builtin_clzg(0u, 32) == 32, "clzg zero with fallback");
  __CPROVER_assert(__builtin_ctzg(a) == 20, "ctzg");
  __CPROVER_assert(__builtin_ctzg(0ul, 64) == 64, "ctzg zero with fallback");
  __CPROVER_assert(__builtin_clzg(a) == 12, "WRONG (must FAIL)");
}
