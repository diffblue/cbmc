// Debian package pixman

#define static_assert(x) ((struct { int field : (x)?1:-1; } *)0)

int main()
{
  #if defined(__GNUC__)
  unsigned int __attribute__((vector_size (4*sizeof(unsigned int)))) v1 = { 1, 1, 1, 1 };
  unsigned int __attribute__((vector_size (4*sizeof(unsigned int)))) v3 = { 3, 3, 3, 3 };

  static_assert(sizeof(v1==v3)==sizeof(int)*4);

  // accepted by GCC, but not Clang
  #ifndef __clang__
  int condition;
  condition=(v3 == (v1<<1)+v1)[0];
  #endif
  #endif

  return 0;
}
