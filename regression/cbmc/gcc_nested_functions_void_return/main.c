// Regression test: a nested function whose return type (here void) differs
// from the enclosing function's return type (here int) must not clobber the
// enclosing function's return type. Previously this crashed goto conversion
// with "function has return void but a return statement returning signed int"
// followed by an invariant violation in convert_return.
int main(void)
{
  int x = 0;

  void set_x(void)
  {
    x = 1;
  }

  set_x();

  __CPROVER_assert(x == 1, "nested void function updated captured variable");

  return 0;
}
