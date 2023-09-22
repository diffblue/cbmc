int main()
{
  int x;
  __CPROVER_size_t x_i;
  _Static_assert(sizeof(&x) == sizeof(x_i), "pointer width");
  __CPROVER_assert(((__CPROVER_size_t)&x & 0x1ULL) == 0, "LSB is zero");
  x_i = (__CPROVER_size_t)&x >> 1;
  x_i <<= 1;
  __CPROVER_assert(*(int *)x_i == x, "pointer to x is tracked through shifts");
}
