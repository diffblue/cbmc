int a = 0;       // should be havoced
const int b = 0; // should not be havoced (const)
int c = 0;       // should be havoced

void foo() __CPROVER_requires(1) __CPROVER_ensures(1) __CPROVER_assigns()
{
  if(a)
    __CPROVER_assert(0, "guarded by a");

  if(b)
    __CPROVER_assert(0, "guarded by b");

  if(c)
    __CPROVER_assert(0, "guarded by c");
}

void main()
{
  foo();
}
