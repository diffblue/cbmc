int main()
{
  unsigned x;
  __CPROVER_assume(x > 0);
  union U {
    unsigned A[x];
  };
  int i, i_before;
  i_before = i;
  union U u = *((union U *)&i);
  i = u.A[0];
  __CPROVER_assert(i == i_before, "going through union works");
}
