int main()
{
  int i, j = __VERIFIER_nondet_int();

  i=1;

  if(j)
    goto l;

  i=2;

 l:;

  assert(i==1 || !j);
}
