int calls;
const char *last;
void marker(const char *function)
{
  ++calls;
  last = function;
}
void foo(void)
{
  __CPROVER_assert(calls == 2 && last[0] == 'f', "foo is entered");
}
int main()
{
  __CPROVER_assert(calls == 1 && last[0] == 'm', "main is entered");
  foo();
  __CPROVER_assert(calls == 2, "returning does not call the marker");
  return 0;
}
