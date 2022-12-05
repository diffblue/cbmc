int main()
{
  unsigned int arrayOfInt [2];

  int diff1 = &arrayOfInt[1] - arrayOfInt;
  __CPROVER_assert(diff1==1, "pointer diff1");

  unsigned int diff2 = &arrayOfInt [1] - arrayOfInt;
  __CPROVER_assert(diff2==1, "pointer diff2");

  int zero = (char **)8 - (char **)8;
  __CPROVER_assert(zero == 0, "should be zero");

  int ten = (char *)20 - (char *)10;
  __CPROVER_assert(ten == 10, "should be ten");

  return 0;
}
