int main()
{
  // create a union type of non-constant, non-zero size
  unsigned x;
  __CPROVER_assume(x > 0);
  union U
  {
    unsigned A[x];
  };
  // create an integer of arbitrary value
  int i, i_before;
  i_before = i;
  // initialize a union of non-zero size from the integer
  unsigned u = ((union U *)&i)->A[0];
  // reading back an integer out of the union should yield the same value for
  // the integer as it had before
  i = u;
  __CPROVER_assert(i == i_before, "going through union works");
}
