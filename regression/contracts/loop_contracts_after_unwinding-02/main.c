// clang-format off
int lock, g, h;

void m_spin(int *l)
{
  while(*l)
    __CPROVER_assigns()
    __CPROVER_loop_invariant(1)
  {
  }
  *l = 1;
}

void a_acq(void)
{
  while(1)
    __CPROVER_loop_invariant(1)
  {
    m_spin(&lock);
    if(g)
      return;
  }
}

void z_f(void)
{
  do { } while(0);
  a_acq();
  for(int i = 0; i < 10; i++)
    __CPROVER_assigns(i)
    __CPROVER_loop_invariant(0 <= i && i <= 10)
  {
  }
}

int main()
{
  z_f();
}
// clang-format on
