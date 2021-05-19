void a()
{
  // Uses the implicit signature of undefined functions: int c(void)
  int b = c();
  __CPROVER_assert(b == 0, "expected to fail");
}
void c(void)
{
  // Actually... don't return anything
  // So the results will be non-deterministic
}

int main(int argc, char **argv)
{
  a();
  return 0;
}
