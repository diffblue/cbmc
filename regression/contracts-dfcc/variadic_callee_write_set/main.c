int g;

int my_log(const char *fmt, ...)
{
  (void)fmt;
  g = 1;
  return 0;
}

void callee(void)
  // clang-format off
  __CPROVER_assigns(g)
// clang-format on
{
  unsigned short v = 0;
  my_log("%d", v);
}

int main(void)
{
  callee();
  return 0;
}
