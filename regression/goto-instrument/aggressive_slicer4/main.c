// test should fail
// shortest path only is not sufficient to violate assertion,
// but we specifically require that function B is kept, which
// allows path main -> B -> C -> D

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
