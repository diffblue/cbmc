// An extern definition: its type, including its parameter identifiers, must
// not be replaced by that of a declaration in another translation unit.
extern int foo(int *p)
{
  return *p;
}

int main()
{
  int x = 42;
  __CPROVER_assert(foo(&x) == 42, "foo returns *p");
  return 0;
}
