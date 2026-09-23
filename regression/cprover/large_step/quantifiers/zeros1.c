int main()
{
  char array[10];

  __CPROVER_assume(∀ int i; i >= 0 && i<sizeof(array) ==> array[i] == 0);

  __CPROVER_assert(array[3] == 0, "property 1");

  return 0;
}
