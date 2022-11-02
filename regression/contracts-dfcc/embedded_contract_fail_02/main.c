typedef int (*fun_ptr_t)();

int bar()
{
  return 1;
}

void foo(int (*fun_ptr)() __CPROVER_ensures(__CPROVER_return_value == 1))
{
  return;
}

void main()
{
  fun_ptr_t fun_ptr = bar;
  foo(fun_ptr);
  return;
}
