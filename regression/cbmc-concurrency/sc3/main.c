__CPROVER_thread_local int local1;

void f()
{
  int local2;
  
  local1=1;
  local2=1;
  
  local1++;
  local2++;
  
  assert(local1==2);
  assert(local2==2);
}

int main()
{
  __CPROVER_ASYNC_1: f();
  f();
}
