// N5008 [lex.string]/9: evaluating a string literal results in a string
// literal object with static storage duration; a pointer to its first
// element can be used to access every element
extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  const char16_t *p = u"ab";
  const wchar_t *w = L"cd";
  __CPROVER_assert(p[0] == u'a' && p[1] == u'b' && p[2] == 0, "char16_t");
  __CPROVER_assert(w[1] == L'd' && w[2] == 0, "wchar_t");
  __CPROVER_assert(p[2] == u'a', "WRONG (must FAIL)");
}
