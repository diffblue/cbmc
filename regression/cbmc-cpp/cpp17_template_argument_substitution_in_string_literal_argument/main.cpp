extern "C" void __CPROVER_assert(bool, const char *);
template <class C>
constexpr const C *widen(const char *narrow, const wchar_t *wide)
{
  if constexpr(sizeof(C) == 1)
    return narrow;
  else
    return wide;
}
template <class C>
struct spec
{
  // N5008 [temp.inst]/3: instantiating the member substitutes C in the
  // call, whose arguments include the wide string literal (an array
  // constant) -- the shape of GCC 16's _GLIBCXX_WIDEN in <chrono>
  static constexpr const C *chars = widen<C>("0123", L"0123");
  static constexpr C third = chars[2];
};
int main()
{
  __CPROVER_assert(spec<char>::third == '2', "narrow");
  __CPROVER_assert(spec<wchar_t>::third == L'2', "wide");
  __CPROVER_assert(spec<wchar_t>::third == L'3', "WRONG (must FAIL)");
  return 0;
}
