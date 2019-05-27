struct S
{
  int i;
};

int main()
{
  unsigned x;
  __CPROVER_assume(x % sizeof(int) == 0);
  struct S A[x];
  ((char *)A)[x] = 42;
  __CPROVER_assert((A[x / sizeof(int)].i & 0xFF) == 42, "lowest byte is 42");
}
