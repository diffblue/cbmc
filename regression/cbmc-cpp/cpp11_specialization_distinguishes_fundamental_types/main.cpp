// N5008 [basic.fundamental]/1, /8-9, [temp.type]/1: char, signed char and
// unsigned char, wchar_t and int, char16_t and unsigned short, and long
// and long long are distinct types, so they select different
// specializations and __is_same tells them apart; [conv.prom]/2 promotes
// wchar_t and char32_t to their underlying types
extern "C" void __CPROVER_assert(bool, const char *);
template <class T>
struct kind
{
  static const int value = 0;
};
template <>
struct kind<signed char>
{
  static const int value = 1;
};
template <>
struct kind<wchar_t>
{
  static const int value = 2;
};
template <>
struct kind<long long>
{
  static const int value = 3;
};
template <>
struct kind<char16_t>
{
  static const int value = 4;
};
template <class T>
struct named
{
  int get()
  {
    return 0;
  }
};
template <>
struct named<signed char>
{
  int get()
  {
    return 1;
  }
};
int main()
{
  __CPROVER_assert(
    kind<char>::value == 0 && kind<signed char>::value == 1,
    "char and signed char");
  __CPROVER_assert(
    kind<int>::value == 0 && kind<wchar_t>::value == 2, "int and wchar_t");
  __CPROVER_assert(
    kind<long>::value == 0 && kind<long long>::value == 3,
    "long and long long");
  __CPROVER_assert(
    kind<unsigned short>::value == 0 && kind<char16_t>::value == 4,
    "unsigned short and char16_t");
  named<char> c;
  __CPROVER_assert(c.get() == 0, "member of the primary");
  __CPROVER_assert(
    !__is_same(int, wchar_t) && !__is_same(char, signed char) &&
      !__is_same(long, long long) && __is_same(wchar_t, wchar_t),
    "__is_same");
  // [conv.prom]/2: they are promoted to their underlying types
  char32_t c32 = U'a';
  wchar_t w = L'b';
  __CPROVER_assert(
    kind<decltype((c32 << 11) | 0x7ffu)>::value == 0 &&
      __is_same(decltype(c32 | 1u), unsigned int) &&
      __is_same(decltype(w + 0), int) && __is_same(decltype(c32), char32_t),
    "promotion");
  __CPROVER_assert(kind<wchar_t>::value == 0, "WRONG (must FAIL)");
}
