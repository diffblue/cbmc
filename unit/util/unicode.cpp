/*******************************************************************\

Module: Unicode conversion tests.

Author: Vojtech Forejt, forejtv@diffblue.com

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <vector>
#include <string>
#include <codecvt>
#include <locale>

#include <util/unicode.h>

// the u8 prefix is only available from VS 2015 onwards
#if !defined(_MSC_VER) || _MSC_VER >= 1900

// This unit test compares our implementation with codecvt implementation,
// checking bit-by-bit equivalence of results.

static bool paranoid_wstr_equals(const std::wstring &a, const std::wstring &b)
{
  if(a.size() != b.size())
    return false;
  const char
    *pa=reinterpret_cast<const char *>(&a[0]),
    *pb=reinterpret_cast<const char *>(&b[0]);
  for(std::size_t i=0; i<a.size() * sizeof(a.front()); ++i)
  {
    if(pa[i] != pb[i])
      return false;
  }
  return true;
}

// helper print function, can be called for debugging problem
#if 0
#include <iostream>

static void wstr_print(const std::wstring &a, const std::wstring &b)
{
  int endi=(a.size()>b.size())?a.size():b.size();
  const unsigned char
    *pa=reinterpret_cast<const unsigned char *>(&a[0]),
    *pb=reinterpret_cast<const unsigned char *>(&b[0]);
  for(std::size_t i=0; i<endi * sizeof(a.front()); ++i)
  {
    std::cout << ((a.size()<endi)?"x":std::to_string(pa[i]))
      << ' '
      << ((b.size()<endi)?"x":std::to_string(pb[i])) << '\n';
  }
  std::cout << '\n';
}
#endif

static bool compare_utf8_to_utf16(const std::string &in)
{
  const std::wstring s1 = utf8_to_utf16_native_endian(in);

  typedef std::codecvt_utf8_utf16<wchar_t> codecvt_utf8_utf16t;
  std::wstring_convert<codecvt_utf8_utf16t> converter;
  std::wstring s2=converter.from_bytes(in);

  return paranoid_wstr_equals(s1, s2);
}

TEST_CASE("unicode0", "[core][util][unicode]")
{
  const std::string s = u8"abc";
  REQUIRE(compare_utf8_to_utf16(s));
}

TEST_CASE("unicode1", "[core][util][unicode]")
{
  const std::string s = u8"\u0070\u00DF\u00E0\u00EF\u00F0\u00F7\u00F8";
  REQUIRE(compare_utf8_to_utf16(s));
}

TEST_CASE("unicode2", "[core][util][unicode]")
{
  const std::string s = u8"$¢€𐍈";
  REQUIRE(compare_utf8_to_utf16(s));
}

TEST_CASE("unicode3", "[core][util][unicode]")
{
  const std::string s = u8"𐐏𤭢";
  REQUIRE(compare_utf8_to_utf16(s));
}

TEST_CASE("unicode4", "[core][util][unicode]")
{
  const std::string s = u8"дȚȨɌṡʒʸͼἨѶݔݺ→⅒⅀▤▞╢◍⛳⻥龍ンㄗㄸ";
  REQUIRE(compare_utf8_to_utf16(s));
}
#endif
