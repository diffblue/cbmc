int global;
_Bool flag;

void my_function1()
  // clang-format off
  __CPROVER_assigns(flag: global) // passes
// clang-format on
{
  if(flag)
    global = 10;
}

void my_function2()
  // clang-format off
  __CPROVER_assigns(flag: global) // fails
// clang-format on
{
  global = 10;
}
