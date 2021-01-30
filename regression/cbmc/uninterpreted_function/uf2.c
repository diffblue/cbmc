int __CPROVER_uninterpreted_f(int, int);
__CPROVER_bool __CPROVER_uninterpreted_g(int, int);

main()
{
  int a, b;

  int inst1 = __CPROVER_uninterpreted_f(1, a);
  int inst2 = __CPROVER_uninterpreted_f(1, b);

  if(a == b)
    __CPROVER_assert(inst1 == inst2, "functional consistency for f");

  int inst3 = __CPROVER_uninterpreted_g(1, a);
  int inst4 = __CPROVER_uninterpreted_g(1, b);

  if(a == b)
    __CPROVER_assert(inst3 == inst4, "functional consistency for g");
}
