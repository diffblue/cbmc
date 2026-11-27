// clang-format off
int lock;

void spin(int *l)
{
  while(*l)
    __CPROVER_assigns()
    __CPROVER_loop_invariant(1)
  {
  }
  *l = 1;
}

void acquire(void)
{
  while(1)
    __CPROVER_loop_invariant(1)
  {
    spin(&lock);
  }
}

void f(void)
{
  do { } while(0);
  acquire();
  for(int i = 0; i < 10; i++)
    __CPROVER_assigns(i)
    __CPROVER_loop_invariant(0 <= i && i <= 10)
  {
  }
}

int main()
{
  f();
}
// clang-format on
