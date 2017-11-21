void D()
{
  __CPROVER_assert(0,"");
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

  switch(nondet)
  {
    case 1: B(); break;
    case 3: C(); break;
    default: break;
  }
return 0;
}