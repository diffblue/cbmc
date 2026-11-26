int __CPROVER_uninterpreted_f(int);
int nondet_int(void);
int main()
{
  int x = nondet_int(), y = nondet_int();
  __CPROVER_assert(x != 1, "not one");
  __CPROVER_assert(
    x != y || __CPROVER_uninterpreted_f(x) == __CPROVER_uninterpreted_f(y),
    "functional consistency");
  return 0;
}
