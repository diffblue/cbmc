int main()
{
  int x = 123;

  // The loops do not assign x.
  for(int i = 0; i < 10; i++)
    ;
  for(int i = 0; i < 10; i++)
    ;

  __CPROVER_assert(x == 123, "property 1"); // passes
}
