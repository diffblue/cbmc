#define static_assert(x) ((struct { int field : (x)?1:-1; } *)0)

int main()
{
  #if defined(__GNUC__)
  // accepted by GCC, but not Clang
  #ifndef __clang__
  // unqualified __auto_type
  __auto_type s=1;
  __auto_type u=1U;

  static_assert(__builtin_types_compatible_p(typeof(s), int));
  static_assert(__builtin_types_compatible_p(typeof(u), unsigned));

  // qualified __auto_type: 'const __auto_type c = s;' is equivalent to
  // 'const typeof(s) c = s;'. The deduced type is int, and the const must be
  // applied. __builtin_types_compatible_p ignores *top-level* qualifiers, so
  // the qualifier is observed via typeof(&...), where the pointee qualifier is
  // significant: the address of a const int is a 'const int *'.
  const __auto_type c = s;
  static_assert(__builtin_types_compatible_p(typeof(c), int));
  static_assert(__builtin_types_compatible_p(typeof(&c), const int *));
  static_assert(!__builtin_types_compatible_p(typeof(&c), int *));

  // a single non-const qualifier
  volatile __auto_type v = s;
  static_assert(__builtin_types_compatible_p(typeof(&v), volatile int *));
  static_assert(!__builtin_types_compatible_p(typeof(&v), int *));

  // a multi-qualifier list, to confirm the whole type_qualifier_list is merged
  const volatile __auto_type cv = s;
  static_assert(
    __builtin_types_compatible_p(typeof(&cv), const volatile int *));
#  endif
#endif
  return 0;
}
