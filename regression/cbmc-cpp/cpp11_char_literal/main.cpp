// C++ character literal types (N5008 [lex.ccon])
#include <type_traits>

int main()
{
  // An ordinary character literal has type char (not int as in C).
  static_assert(std::is_same<decltype('a'), char>::value, "ordinary -> char");
  __CPROVER_assert(sizeof('a') == 1, "sizeof ordinary char literal is 1");

  // Prefixed character literals carry their designated types.
  static_assert(std::is_same<decltype(L'a'), wchar_t>::value, "L -> wchar_t");
  static_assert(std::is_same<decltype(u'a'), char16_t>::value, "u -> char16_t");
  static_assert(std::is_same<decltype(U'a'), char32_t>::value, "U -> char32_t");

  // A multicharacter literal has type int.
  static_assert(std::is_same<decltype('ab'), int>::value, "multichar -> int");

  // The value is preserved.
  __CPROVER_assert('A' == 65, "char value preserved");

  return 0;
}
