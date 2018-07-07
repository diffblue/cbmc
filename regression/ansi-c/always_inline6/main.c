static inline __attribute__((__always_inline__)) int func(int val, ...)
{
  return val + 1;
}

int main()
{
  int x;
  return func(x, x);
}
