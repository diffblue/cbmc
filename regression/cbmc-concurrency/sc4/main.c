int global;

int main()
{
  global=1;
  global=2;
  
  __CPROVER_ASYNC_1: assert(global==2);
  
  assert(global==2);
}
