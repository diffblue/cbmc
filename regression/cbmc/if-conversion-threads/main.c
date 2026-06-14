int x;
_Bool done;
void t(void)
{
  x = 5;
  done = 1;
}
int main()
{
  int c = 0;
__CPROVER_ASYNC_1:
  t();
  if(c)
    x = 1;
  __CPROVER_assume(done);
  __CPROVER_assert(x == 5, "thread's write is not lost");
  return 0;
}
