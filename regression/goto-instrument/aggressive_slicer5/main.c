// Test should fail. Shortest path only is not sufficient
// due to assumption that nondet !=3, but
// preserve-all-direct-paths preserves the path main -> B -> C -> D.

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
