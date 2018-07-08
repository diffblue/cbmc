static inline __attribute__((__always_inline__)) int func(int val)
{
  val = val + 1;
  return val;
}

int main()
{
  int x;
  return func(x);
}
