int __isoc99_sscanf(const char *, const char *, ...);

int main()
{
  int x;
  // The model of __isoc99_sscanf calls vsscanf, which glibc 2.38 and later
  // redirect to __isoc23_vsscanf with _GNU_SOURCE. That function has no
  // model.
  int r = __isoc99_sscanf("1", "%d", &x);
  __CPROVER_assert(r <= 1, "result");
  return 0;
}
