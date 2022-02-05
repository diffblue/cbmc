
int main()
{
  int i;
  for(i = 0; i < 10; i++) {}
  __CPROVER_assert(0, "fails when fully unwinding the loop");
}
