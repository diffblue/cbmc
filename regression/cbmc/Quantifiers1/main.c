int zero_array[10];

int main()
{
  // C# style
  assert(__CPROVER_forall { int i; (i>=0 && i<10) ==> zero_array[i]==0 });

  // ACSL style
  assert(\forall int i; ((i>=0 && i<10) ==> (zero_array[i]==0)));

  // the operand gets converted implicitly to bool
  assert(\forall int i; 2);

  const unsigned N=10;
  unsigned i=0;
  char c[N];

  for(i=0; i<N; ++i)
    c[i]=i;

  assert(__CPROVER_forall {unsigned i; i>9 || c[i]==i});
  return 0;
}
