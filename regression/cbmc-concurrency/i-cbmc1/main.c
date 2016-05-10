int global;

void isrB()
{
  global=3;
  assert(global==3); // safe
}

void isrA()
{
  __CPROVER_ASYNC_1: isrB();
  global=2;
}

int main()
{
  __CPROVER_ASYNC_1: isrA();
  global=1;
  return 0;
}
