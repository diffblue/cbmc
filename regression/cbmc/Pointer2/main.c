int main()
{
  int x;
  unsigned long long x_i;
  _Static_assert(sizeof(&x) == sizeof(x_i), "pointer width");
  __CPROVER_assert(((unsigned long long)&x & 0x1ULL) == 0, "LSB is zero");
  x_i = (unsigned long long)&x >> 1;
  x_i <<= 1;
  __CPROVER_assert(*(int *)x_i == x, "pointer to x is tracked through shifts");
}
