#define static_assert(x) ((struct { int field : (x)?1:-1; } *)0)

int main()
{
  #if defined(__GNUC__)
  // accepted by GCC, but not Clang
  #ifndef __clang__
  __auto_type s=1;
  __auto_type u=1U;

  static_assert(__builtin_types_compatible_p(typeof(s), int));
  static_assert(__builtin_types_compatible_p(typeof(u), unsigned));
  #endif
  #endif
  return 0;
}
