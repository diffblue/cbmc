int global;

int main()
{
  __CPROVER_ASYNC_1: if(global==3) global=1;
  global=2;
  assert(global==2); // safe
  global=3;
}
