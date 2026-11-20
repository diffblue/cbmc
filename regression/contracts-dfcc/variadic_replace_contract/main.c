int g;

int my_log(int n, ...)
  // clang-format off
  __CPROVER_requires(n == 1)
  __CPROVER_assigns(g)
  __CPROVER_ensures(__CPROVER_return_value == 7)
// clang-format on
;

int main(void)
{
  int r = my_log(1, 42);
  __CPROVER_assert(r == 7, "contract replaced");
  return 0;
}
