int g;

int my_log(const char *fmt, ...)
{
  (void)fmt;
  g = 1;
  return 0;
}

void callee(void)
  // clang-format off
  __CPROVER_requires(1)
  __CPROVER_assigns()
// clang-format on
{
  unsigned short v;
  my_log("%d", v);
}

int main(void)
{
  callee();
  return 0;
}
