// N5008 [lex.ccon], [basic.fundamental]: char8_t string and character
// literals.
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  const char8_t *s = u8"x";
  __CPROVER_assert(s[0] == u8'x', "char8_t");
  __CPROVER_assert(false, "WRONG (must FAIL)");
}
