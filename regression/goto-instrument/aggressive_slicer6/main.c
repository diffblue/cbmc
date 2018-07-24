// Test should fail
// Assertion in D is reachable when call depth of 1 is preserved,
// Shortest path = main -> C -> D, which is not possible due to assumption
// nondet!=3, but call depth 1 preserves the body of function B, which can also reach
// C.

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
