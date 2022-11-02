#define SIZE 10

void foo(char *in1, char *in2)
  // clang-format off
  __CPROVER_requires(
    __CPROVER_is_fresh(in1, SIZE) &&
    __CPROVER_is_fresh(in2, SIZE))
// clang-format on
{
}

int nondet_int();

int main()
{
  char in1[SIZE];
  char in2[SIZE];
  foo(nondet_int() ? in1 : in2, in2);
  return 0;
}
