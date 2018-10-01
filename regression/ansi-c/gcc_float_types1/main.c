// for gcc, __float80 and __float128 are typedefs
// for clang, __float128 is a keyword, and __float80 doesn't exist.

#if defined(__clang__) || \
    !(defined(__ia64__) || defined(__x86_64__) || defined(__i386__))
int __float80;
#if (defined(__hppa__) || defined(__powerpc__))
__float128 f128;
#endif
#else
__float80 f80;
__float128 f128;
#endif

int main()
{
  #ifndef __clang__
  // on gcc, they can be re-declared, as they are identifiers, not keywords
  int __float80;
  int __float128;
  #endif
}
