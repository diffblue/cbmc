int main()
{
  int i, j = __VERIFIER_nondet_int();

  i = 1;

  if(j > 0)
    j += i;
  else
    j = 0;

  assert(i != j);
}
