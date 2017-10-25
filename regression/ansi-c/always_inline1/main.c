// this is a GCC extension

#ifdef __GNUC__
static inline __attribute__((always_inline))
_Bool __is_kfree_rcu_offset(unsigned long offset)
{
  return offset < 4096;
}

static inline __attribute__((always_inline))
void kfree_rcu(unsigned long offset)
{
  ((void)sizeof(char[1 - 2*!!(!__builtin_constant_p(offset))]));

  ((void)sizeof(char[1 - 2*!!(!__is_kfree_rcu_offset(offset))]));
}

static inline __attribute__((always_inline))
void unused(unsigned long offset)
{
  ((void)sizeof(char[1 - 2*!!(!__builtin_constant_p(offset))]));
}

// unused, but no 'static'
inline __attribute__ ((__always_inline__)) int also_unused(int _c)
{
  return _c;
}
#endif

int main()
{
  #ifdef __GNUC__
  kfree_rcu(42);
  #endif

  return 0;
}
