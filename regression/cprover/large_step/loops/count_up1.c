_Bool nondet_bool();

int main()
{
  int i, j;

  i = j;

  while(nondet_bool())
  {
    i++;
    j++;
  }

  __CPROVER_assert(i == j, "property 1"); // passes

  return 0;
}
