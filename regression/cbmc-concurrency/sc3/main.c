__CPROVER_thread_local int local1;

#ifdef __GNUC__
__thread int local2;
#else
__CPROVER_thread_local int local2;
#endif

void f()
{
  int local3;
  
  local1=1;
  local2=1;
  local3=1;
  
  local1++;
  local2++;
  local3++;
  
  assert(local1==2);
  assert(local2==2);
  assert(local3==2);
}

int main()
{
  __CPROVER_ASYNC_1: f();
  f();
}
