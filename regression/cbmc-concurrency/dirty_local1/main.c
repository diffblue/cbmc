int * global_ptr;

void f()
{
  *global_ptr=42;
}

int main()
{
  int a=0;
  global_ptr=&a;
  __CPROVER_ASYNC_1: f();
  assert(a==0);
}

