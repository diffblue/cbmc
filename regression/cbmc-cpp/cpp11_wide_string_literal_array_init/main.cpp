extern "C" void __CPROVER_assert(bool, const char *);
int main()
{
  const wchar_t w[] = L"de";
  __CPROVER_assert(
    w[1] == L'e' && sizeof(w) == 3 * sizeof(wchar_t),
    "wide string literal initializes an unbounded array");
  const char16_t u[] = u"xyz";
  __CPROVER_assert(
    sizeof(u) == 4 * sizeof(char16_t) && u[2] == u'z', "char16_t literal");
  const char32_t U[] = U"q";
  __CPROVER_assert(sizeof(U) == 2 * sizeof(char32_t), "char32_t literal");
  const char c[] = "ab";
  __CPROVER_assert(sizeof(c) == 3, "narrow");
  __CPROVER_assert(w[0] == L'e', "WRONG (must FAIL)");
}
