struct S
{
  unsigned char A[1];
  char len; // keep this to reproduce
};

struct O
{
  struct S A[2];
  char len; // this is key to reproduce
};

int main()
{
  struct O t = {{{{0}, 2}, {{42}, 2}}, 2};
  unsigned n;
  __CPROVER_assume(n < 2);
  __CPROVER_assume(n > 0);
  char src_n[n];
  __CPROVER_array_replace((char *)t.A[0].A, src_n);
  __CPROVER_assert(t.A[1].A[0] == 42, "");
}
