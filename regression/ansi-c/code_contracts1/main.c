int foo()
__CPROVER_ensures(__CPROVER_forall {int i; 1 == 1})
{
  return 1;
}

int bar()
__CPROVER_ensures(__CPROVER_forall {int i; 1 == 1} &&
                  __CPROVER_return_value == 1)
{
  return 1;
}

int main() {
  foo();
  bar();
}
