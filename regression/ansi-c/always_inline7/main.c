static inline __attribute__((__always_inline__)) int func(int val)
{
  int local = val;
  return local;
}

int main()
{
  int x;
  return func(x);
}
