typedef void (*fun_ptr_t)(int x);

void bar(int x)
{
  return;
}

void foo(void (*fun_ptr)(int x) __CPROVER_requires(x != 0))
{
  return;
}

void main()
{
  fun_ptr_t fun_ptr = bar;
  foo(fun_ptr);
  return;
}
