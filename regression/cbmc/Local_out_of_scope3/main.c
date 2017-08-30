unsigned int *GLOBAL_POINTER[1];

int index;

void f(void)
{
  unsigned int actual=0u;
  GLOBAL_POINTER[0] = &actual;

  if(index==0)
    *GLOBAL_POINTER[index] = 1u;
  else
    actual = 2u;

  __CPROVER_assume(1u == actual);
}

void main(void)
{
  index=nondet_int();
  f();
  f();
  __CPROVER_assert(0==1, "");
}
