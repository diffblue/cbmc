int x;
int other;
void isr(void)
{
  x = 1;
}
int main()
{
  other = 2;
  int v = x;
  __CPROVER_assert(v == 0, "the handler may run before a read");
  __CPROVER_assert(v == 1, "the handler need not run before a read");
  return 0;
}
