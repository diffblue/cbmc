// Test should fail
// Assertion in D is reachable by main -> C -> D
// Assertion in E is reachable by main -> E

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

void E()
{
  __CPROVER_assert(0, "");
}

int main()
{
  int nondet;

  switch(nondet)
  {
  case 1:
    B();
    break;
  case 2:
    E();
    break;
  case 3:
    C();
    break;
  default:
    break;
  }
  return 0;
}
