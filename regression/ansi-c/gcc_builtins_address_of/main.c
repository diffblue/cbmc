#ifdef __GNUC__

int main()
{
  void (*f)(int) = __builtin_exit;
  int (*g)(float) = __builtin_isnanf;
  int (*h)(int) = __builtin_ffs;
  void *(*m)(__SIZE_TYPE__) = __builtin_malloc;
  void *(*c)(void *, const void *, __SIZE_TYPE__) = __builtin_memcpy;
  (void)g(3.14f);
  (void)h(42);
  f(1);
  return 0;
}

#else

int main()
{
}

#endif
