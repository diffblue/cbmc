int global;

void isrA()
{
  global=2;
}

void isrB()
{
  __CPROVER_ASYNC_1: isrA();
  global=3;
  assert(global==3); // fail
}

int main()
{
  __CPROVER_ASYNC_1: isrB();
  global=1;
  return 0;
}
