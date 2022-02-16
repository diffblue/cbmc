int main()
{
  unsigned int a;
  unsigned int b = 12;
  __CPROVER_assume(a > 15);

  // expected to fail by assigning a = 4294967284u in the trace
  // and wrapping around to 0, which results in 0 > 27.
  __CPROVER_assert(a + b > 27, "a plus b should be more than 27");
  // expected to fail by assigning a = 2147483648u in the trace
  // and evaluating to 2147483660 > 27, which is true.
  __CPROVER_assert(!(a + b > 27), "a plus b should be more than 27");

  // Same round of tests but for unsigned long long.
  unsigned long long int c;
  unsigned long long int d = 12llu;
  __CPROVER_assume(c > 15llu);

  __CPROVER_assert(c + d > 27, "c plus d should be more than 27");
  __CPROVER_assert(!(c + d > 27), "c plus d should be more than 27");
}
