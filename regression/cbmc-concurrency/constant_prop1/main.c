void thread_c(int t)
{
  int l=t;
  __CPROVER_assert(t==42, "t==42 by constant propagation");
}

void thread_nc(int t)
{
  int l=t;
  __CPROVER_assert(t<42, "t<42");
}

static void spawner_c(int constant)
{
__CPROVER_ASYNC_1:
  thread_c(constant);
}

static void spawner_nc(int not_constant)
{
__CPROVER_ASYNC_1:
  thread_nc(not_constant);
}

int main()
{
  int x;
  __CPROVER_assume(x<42);

  // spawner_nc(x);

  if(x)
    spawner_c(42);

  return 0;
}
