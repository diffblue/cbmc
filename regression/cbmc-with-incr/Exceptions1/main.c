int global;

void test_try_finally1()
{
  __CPROVER_try
  {
    global=1;
  }
  __CPROVER_finally
  {
    global=2;
  }
  
  assert(global==2);
}

void helper()
{
  __CPROVER_try
  {
    global=1;
    return;
    global=2;
  }
  __CPROVER_finally
  {
    global=3;
  }
  
  assert(global==2);
}

void test_try_finally2()
{
  helper();
  assert(global==3);
}

void test_try_catch1()
{
  __CPROVER_try
  {
    global=1;
  }
  __CPROVER_catch
  {
    global=2;
  }
  
  assert(global==1);
}

void test_try_catch2()
{
  __CPROVER_try
  {
    global=1;
    __CPROVER_throw;
    global=2;
  }
  __CPROVER_catch
  {
    global=3;
  }
  
  assert(global==3);
}

int main()
{
  test_try_finally1();
  test_try_finally2();
  test_try_catch1();
  test_try_catch2();
}

