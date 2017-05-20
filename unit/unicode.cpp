/*******************************************************************\

Module: Unicode conversion tests.

Author: Vojtech Forejt, forejtv@diffblue.com

\*******************************************************************/

#include <cassert>
#include <vector>
#include <string>
#include <codecvt>
#include <iomanip>
#include <iostream>
#include <locale>

#include <util/unicode.h>

// This unit test compares our implementation with codecvt implementation,
// checking bit-by-bit equivalence of results.

bool paranoid_wstr_equals(const std::wstring &a, const std::wstring &b)
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
void wstr_print(const std::wstring &a, const std::wstring &b)
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

void compare_utf8_to_utf16_big_endian(std::string& in)
{
  std::wstring s1=utf8_to_utf16_big_endian(in);

  typedef std::codecvt_utf8_utf16<wchar_t> codecvt_utf8_utf16t;
  std::wstring_convert<codecvt_utf8_utf16t> converter;
  std::wstring s2=converter.from_bytes(in);

  assert(paranoid_wstr_equals(s1, s2));
}

void compare_utf8_to_utf16_little_endian(std::string& in)
{
  std::wstring s1=utf8_to_utf16_little_endian(in);

  const std::codecvt_mode mode=std::codecvt_mode::little_endian;
  const unsigned long maxcode=0x10ffff;

  typedef std::codecvt_utf8_utf16<wchar_t, maxcode, mode> codecvt_utf8_utf16t;
  std::wstring_convert<codecvt_utf8_utf16t> converter;
  std::wstring s2=converter.from_bytes(in);

  assert(paranoid_wstr_equals(s1, s2));
}

int main()
{
  std::string s;
  s=u8"\u0070\u00DF\u00E0\u00EF\u00F0\u00F7\u00F8";
  compare_utf8_to_utf16_big_endian(s);
  compare_utf8_to_utf16_little_endian(s);
  s=u8"$¢€𐍈";
  compare_utf8_to_utf16_big_endian(s);
  compare_utf8_to_utf16_little_endian(s);
  s=u8"𐐏𤭢";
  compare_utf8_to_utf16_big_endian(s);
  compare_utf8_to_utf16_little_endian(s);
  s=u8"дȚȨɌṡʒʸͼἨѶݔݺ→⅒⅀▤▞╢◍⛳⻥龍ンㄗㄸ";
  compare_utf8_to_utf16_big_endian(s);
  compare_utf8_to_utf16_little_endian(s);
}

