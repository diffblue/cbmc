int __CPROVER_uninterpreted_f(int, int);

main()
{
  int a, b;

  int inst1 = __CPROVER_uninterpreted_f(1, a);
  int inst2 = __CPROVER_uninterpreted_f(1, b);

  if(a == b)
    __CPROVER_assert(inst1 == inst2, "functional consistency");
}
