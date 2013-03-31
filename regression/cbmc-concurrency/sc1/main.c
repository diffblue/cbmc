int global;

int main()
{
  __CPROVER_ASYNC_1: global=1;
  global=2;
  assert(global==2); // to fail
}
