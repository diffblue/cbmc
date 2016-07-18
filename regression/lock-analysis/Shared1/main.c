int x;

int f()
{
  x++;
}

void th1()
{
  f();
}

void th2()
{
  f();
}


int main()
{
  x=0;

  __CPROVER_ASYNC_1: th1();
  __CPROVER_ASYNC_2: th2();
}
