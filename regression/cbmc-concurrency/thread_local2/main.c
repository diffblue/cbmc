int __CPROVER_thread_local thlocal = 4;

int main()
{
  int loc;

  loc = 123;

__CPROVER_ASYNC_3:
  thlocal = loc, __CPROVER_assert(thlocal == 123, "hello");
}
