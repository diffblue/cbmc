void *nondet_pointer(void);
unsigned nondet_unsigned(void);

int main()
{
  unsigned n = nondet_unsigned();
  __CPROVER_assume(n > 0 && n < 4);
  // A member of non-constant size that is not the last member: this struct
  // has no byte layout.
  struct S
  {
    int a[n];
    int b;
  };

  // dereferencing an unknown pointer
  struct S *p = nondet_pointer();
  int x = p->b;
  __CPROVER_assert(x == 42 || x != 42, "tautology");

  // dereferencing an integer address
  struct S *q = (struct S *)(__CPROVER_size_t)1024;
  int y = q->b;
  __CPROVER_assert(y == 42, "unconstrained value");
  return 0;
}
