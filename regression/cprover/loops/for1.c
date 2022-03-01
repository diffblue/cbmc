int main()
{
  int i;

  for(i = 0; i < 10; i++)
    ;

  __CPROVER_assert(i == 10, "property 1"); // passes

  return 0;
}
