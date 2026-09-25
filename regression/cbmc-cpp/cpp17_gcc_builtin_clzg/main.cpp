// GCC 14's type-generic bit builtins (GCC reference, "Other Built-in
// Functions"): `int __builtin_clzg(T arg [, int value])' and __builtin_ctzg
// for any unsigned integer type T, the optional second argument being the
// result for arg == 0.  libstdc++ 14+'s std::countl_zero / bit_width
// (`__builtin_clzg(__x, __int_traits<_Tp>::__digits)') are built on them --
// behind the gcc16 map/vector KNOWNBUGs.  Declared as `int f(int)', the
// two-argument form had no match.
extern "C" void __CPROVER_assert(bool, const char *);
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
