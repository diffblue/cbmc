int main()
{
  int i = __VERIFIER_nondet_int();

  switch(i)
  {
  case 0:
  case 1:
    assert(i==0 || i==1);
    break;

  case 2:
    assert(i==2);
    break;

  default:
    assert(i!=0 && i!=1 && i!=2);
  }
}
