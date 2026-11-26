// N5008 [lex.icon]: the uz integer-literal suffix.
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  auto n = 3uz;
  __CPROVER_assert(
    sizeof(n) == sizeof(decltype(sizeof 0)) && n == 3, "uz suffix");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
