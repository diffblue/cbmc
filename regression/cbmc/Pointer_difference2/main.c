int main()
{
  int array[4];
  int other_array[2];

  __CPROVER_assert(&array[0] - &array[2] == -2, "correct");

  int diff = array - other_array;
  _Bool nondet;
  if(nondet)
    __CPROVER_assert(diff != 42, "undefined behavior");
  else
    __CPROVER_assert(diff == 42, "undefined behavior");

  __CPROVER_assert(
    ((char *)(&array[3])) - ((char *)(&array[1])) == 2 * sizeof(int),
    "casting works");

  int *p = &array[3];
  ++p;
  __CPROVER_assert(p - &array[0] == 4, "end plus one works");
  __CPROVER_assert(p - &array[0] != 3, "end plus one works");
  ++p;
  _Bool nondet_branch;
  if(nondet_branch)
    __CPROVER_assert(p - &array[0] == 5, "end plus 2 is nondet");
  else
    __CPROVER_assert(p - &array[0] != 5, "end plus 2 is nondet");

  return 0;
}
