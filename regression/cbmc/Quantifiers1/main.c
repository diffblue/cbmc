int zero_array[10];

int main()
{
  // C# style
  assert(__CPROVER_forall { int i; (i>=0 && i<10) ==> zero_array[i]==0 });

  // ACSL style
  assert(\forall int i; ((i>=0 && i<10) ==> (zero_array[i]==0)));
}
