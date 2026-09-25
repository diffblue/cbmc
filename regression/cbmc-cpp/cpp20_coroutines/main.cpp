// C++20 coroutines — minimal test for co_return/co_await/co_yield parsing
void f()
{
  co_return;
}

void g(int x)
{
  int y = co_await x;
  co_yield y;
  co_return;
}

int main()
{
  f();
  __CPROVER_assert(1, "coroutine keywords parsed");
  return 0;
}
