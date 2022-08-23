#define SIZE 10

void foo(char *in) __CPROVER_requires(__CPROVER_is_fresh(in, SIZE))
{
}

int nondet_int();
int main()
{
  char in1[SIZE];
  char in2[SIZE - 1];
  foo(nondet_int() ? in1 : in2);
  return 0;
}
