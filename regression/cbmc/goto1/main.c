int main()
{
  int i = __VERIFIER_nondet_int(), j = __VERIFIER_nondet_int();

  if(i)
    goto l;

  if(j)
    goto l;

  assert(!i && !j);

 l:;
}
