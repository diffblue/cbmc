// A pointer cannot be compared with a floating-point number (C11 6.5.8p2,
// 6.5.9p2).
int f(int *p, double d)
{
  return p == d;
}

int main(void)
{
  return 0;
}
