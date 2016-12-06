// simplified version of openbsd_cmemrchr-alloca_true-valid-memsafety.i

int main() {
  long n;
  __CPROVER_assume(n>=1);

  char X;
  char* s = &X;

  const char *cp;
  cp = s + n; // loses high bits of n for any bits above offset_bits

  //long cp_l=(long)cp;
  //long s_l=(long)s;
  //long n_l=(long)n;
  //long s_n=(long)s+n;

  __CPROVER_assert((long)cp == (long)s + n, "");

  return 0;
}
