int main()
{
  unsigned x = __VERIFIER_nondet_unsigned();
  int i = __VERIFIER_nondet_int();
  int a[100];
  __CPROVER_havoc_object(a);

  // this is guaranteed not to be a buffer overflow
  if(x < 100 && a[x])
  {
    i++;
  }

  __CPROVER_assume(i < 100);

  // this is guaranteed not to be a buffer underflow
  if(i >= 0 && a[i])
  {
    i++;
  }
}
