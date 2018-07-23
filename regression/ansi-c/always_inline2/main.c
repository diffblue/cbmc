static inline __attribute__((__always_inline__)) int func(int val)
{
  return val;
}

static inline int func2(int *p)
{
  // the typecast, although redundant, is essential to show the problem
  return func(*(int*)p);
}

int main()
{
  int x;
  return func2(&x);
}
