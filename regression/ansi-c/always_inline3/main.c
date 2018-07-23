static inline __attribute__((__always_inline__)) int func(int val)
{
  if(val > 0)
    return func(val - 1);
  return 0;
}

int main()
{
  int x;
  return func(x);
}
