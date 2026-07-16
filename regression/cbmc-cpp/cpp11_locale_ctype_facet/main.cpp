// N5008 [locale.general]/8: at program startup the global locale is
// std::locale::classic(), the "C" locale.  C99 7.4 defines the "C"-locale
// character classes: isdigit is exactly '0'..'9', isspace the six standard
// white-space characters, isupper 'A'..'Z', punctuation the printing
// characters that are neither alphanumeric nor space.
//
// libstdc++ initialises the locale facet table inside libstdc++.so, so
// CBMC models the ctype<char> facet of the "C" locale (a static
// classification table + facet object returned by __try_use_facet); this
// exercises the model through the public std::use_facet /
// std::ctype<char>::is interface, positively and negatively.
#include <locale>

int main()
{
  std::locale loc;
  const std::ctype<char> &ct = std::use_facet<std::ctype<char>>(loc);
  __CPROVER_assert(ct.is(std::ctype_base::digit, '5'), "5 is a digit");
  __CPROVER_assert(!ct.is(std::ctype_base::digit, 'a'), "a is not a digit");
  __CPROVER_assert(ct.is(std::ctype_base::alpha, 'a'), "a is alpha");
  __CPROVER_assert(ct.is(std::ctype_base::xdigit, 'a'), "a is xdigit");
  __CPROVER_assert(!ct.is(std::ctype_base::xdigit, 'g'), "g is not xdigit");
  __CPROVER_assert(ct.is(std::ctype_base::space, ' '), "' ' is space");
  __CPROVER_assert(ct.is(std::ctype_base::space, '\t'), "tab is space");
  __CPROVER_assert(!ct.is(std::ctype_base::space, '5'), "5 is not space");
  __CPROVER_assert(ct.is(std::ctype_base::upper, 'Z'), "Z is upper");
  __CPROVER_assert(!ct.is(std::ctype_base::upper, 'z'), "z is not upper");
  __CPROVER_assert(ct.is(std::ctype_base::punct, ','), "comma is punct");
  __CPROVER_assert(!ct.is(std::ctype_base::punct, '7'), "7 is not punct");
  return 0;
}
