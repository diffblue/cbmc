unsigned nondet_unsigned(void);

int main()
{
  int t[2];
  unsigned k = nondet_unsigned();
  __CPROVER_assume(k < 2);
  __CPROVER_assume(__CPROVER_forall {
    unsigned r;
    (r < k) ==> t[r] < 10
  });
  __CPROVER_assume(k == 1);
  __CPROVER_assert(t[0] < 10, "forall with k==1 implies t[0]<10");
}
