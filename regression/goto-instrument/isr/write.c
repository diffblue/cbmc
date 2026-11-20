int flag;
void isr(void)
{
  flag = 1;
}
int main()
{
  flag = 0;
  int v = flag;
  __CPROVER_assert(v == 0, "the handler may run around the write");
  __CPROVER_assert(v == 1, "the handler need not run");
  return 0;
}
