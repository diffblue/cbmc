int main()
{
  int a = 10;
  int nondet_bool;
  int flag = 1;

  int *b = &a;
  int *c = nondet_bool ? &a : 0;
  int *d = flag ? &a : 0;
  int *e;

  // __CPROVER_same_object is True when
  // `__CPROVER_pointer_object(a) == __CPROVER_pointer_object(b)`
  __CPROVER_assert(
    __CPROVER_same_object(b, c), "expected fail as c can be null");
  __CPROVER_assert(
    __CPROVER_same_object(b, d), "expected success because d is &a");
  __CPROVER_assert(
    __CPROVER_same_object(b, e), "expected fail as e can be null");
}
