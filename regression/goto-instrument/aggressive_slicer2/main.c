// test should pass. Shortest path is preserved, main -> C -> D,
// but is not a possible counterexample because of assumption that
// nondet != 3

void D()
{
  __CPROVER_assert(0, "");
}

void C()
{
  int nondet;
  if(nondet)
    D();
}

void B()
{
  C();
};

int main()
{
  int nondet;

  __CPROVER_assume(nondet != 3);
  switch(nondet)
  {
  case 1:
    B();
    break;
  case 3:
    C();
    break;
  default:
    break;
  }
  return 0;
}
