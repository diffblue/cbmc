static inline __attribute__((__always_inline__)) int func(int val)
{
  return (__typeof__(val))42;
}

int main()
{
  int x;
  return func(x);
}
