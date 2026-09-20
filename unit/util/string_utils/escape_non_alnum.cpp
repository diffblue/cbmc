/*******************************************************************\

Module: Unit tests of escape_non_alnum

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// escape_non_alnum Unit Tests

#include <util/string_utils.h>

#include <testing-utils/use_catch.h>

#include <string>
#include <string_view>

using std::string_view_literals::operator""sv;

// test split into two halves to avoid a GCC warning ("variable tracking size
// limit exceeded with -fvar-tracking-assignments, retrying without")
TEST_CASE(
  "escape_non_alnum should work with any single byte character (part 1)",
  "[core][utils][string_utils][escape_non_alnum]")
{
  CHECK(escape_non_alnum("\x00"sv) == "_00");
  CHECK(escape_non_alnum("\x01"sv) == "_01");
  CHECK(escape_non_alnum("\x02"sv) == "_02");
  CHECK(escape_non_alnum("\x03"sv) == "_03");
  CHECK(escape_non_alnum("\x04"sv) == "_04");
  CHECK(escape_non_alnum("\x05"sv) == "_05");
  CHECK(escape_non_alnum("\x06"sv) == "_06");
  CHECK(escape_non_alnum("\x07"sv) == "_07");
  CHECK(escape_non_alnum("\x08"sv) == "_08");
  CHECK(escape_non_alnum("\x09"sv) == "_09");
  CHECK(escape_non_alnum("\x0A"sv) == "_0a");
  CHECK(escape_non_alnum("\x0B"sv) == "_0b");
  CHECK(escape_non_alnum("\x0C"sv) == "_0c");
  CHECK(escape_non_alnum("\x0D"sv) == "_0d");
  CHECK(escape_non_alnum("\x0E"sv) == "_0e");
  CHECK(escape_non_alnum("\x0F"sv) == "_0f");
  CHECK(escape_non_alnum("\x10"sv) == "_10");
  CHECK(escape_non_alnum("\x11"sv) == "_11");
  CHECK(escape_non_alnum("\x12"sv) == "_12");
  CHECK(escape_non_alnum("\x13"sv) == "_13");
  CHECK(escape_non_alnum("\x14"sv) == "_14");
  CHECK(escape_non_alnum("\x15"sv) == "_15");
  CHECK(escape_non_alnum("\x16"sv) == "_16");
  CHECK(escape_non_alnum("\x17"sv) == "_17");
  CHECK(escape_non_alnum("\x18"sv) == "_18");
  CHECK(escape_non_alnum("\x19"sv) == "_19");
  CHECK(escape_non_alnum("\x1A"sv) == "_1a");
  CHECK(escape_non_alnum("\x1B"sv) == "_1b");
  CHECK(escape_non_alnum("\x1C"sv) == "_1c");
  CHECK(escape_non_alnum("\x1D"sv) == "_1d");
  CHECK(escape_non_alnum("\x1E"sv) == "_1e");
  CHECK(escape_non_alnum("\x1F"sv) == "_1f");
  CHECK(escape_non_alnum("\x20"sv) == "_20");
  CHECK(escape_non_alnum("\x21"sv) == "_21");
  CHECK(escape_non_alnum("\x22"sv) == "_22");
  CHECK(escape_non_alnum("\x23"sv) == "_23");
  CHECK(escape_non_alnum("\x24"sv) == "_24");
  CHECK(escape_non_alnum("\x25"sv) == "_25");
  CHECK(escape_non_alnum("\x26"sv) == "_26");
  CHECK(escape_non_alnum("\x27"sv) == "_27");
  CHECK(escape_non_alnum("\x28"sv) == "_28");
  CHECK(escape_non_alnum("\x29"sv) == "_29");
  CHECK(escape_non_alnum("\x2A"sv) == "_2a");
  CHECK(escape_non_alnum("\x2B"sv) == "_2b");
  CHECK(escape_non_alnum("\x2B"sv) == "_2b");
  CHECK(escape_non_alnum("\x2C"sv) == "_2c");
  CHECK(escape_non_alnum("\x2D"sv) == "_2d");
  CHECK(escape_non_alnum("\x2E"sv) == "_2e");
  CHECK(escape_non_alnum("\x2F"sv) == "_2f");
  CHECK(escape_non_alnum("\x30"sv) == "0");
  CHECK(escape_non_alnum("\x31"sv) == "1");
  CHECK(escape_non_alnum("\x32"sv) == "2");
  CHECK(escape_non_alnum("\x33"sv) == "3");
  CHECK(escape_non_alnum("\x34"sv) == "4");
  CHECK(escape_non_alnum("\x35"sv) == "5");
  CHECK(escape_non_alnum("\x36"sv) == "6");
  CHECK(escape_non_alnum("\x37"sv) == "7");
  CHECK(escape_non_alnum("\x38"sv) == "8");
  CHECK(escape_non_alnum("\x39"sv) == "9");
  CHECK(escape_non_alnum("\x3A"sv) == "_3a");
  CHECK(escape_non_alnum("\x3B"sv) == "_3b");
  CHECK(escape_non_alnum("\x3C"sv) == "_3c");
  CHECK(escape_non_alnum("\x3D"sv) == "_3d");
  CHECK(escape_non_alnum("\x3E"sv) == "_3e");
  CHECK(escape_non_alnum("\x3F"sv) == "_3f");
  CHECK(escape_non_alnum("\x40"sv) == "_40");
  CHECK(escape_non_alnum("\x41"sv) == "A");
  CHECK(escape_non_alnum("\x42"sv) == "B");
  CHECK(escape_non_alnum("\x43"sv) == "C");
  CHECK(escape_non_alnum("\x44"sv) == "D");
  CHECK(escape_non_alnum("\x45"sv) == "E");
  CHECK(escape_non_alnum("\x46"sv) == "F");
  CHECK(escape_non_alnum("\x47"sv) == "G");
  CHECK(escape_non_alnum("\x48"sv) == "H");
  CHECK(escape_non_alnum("\x49"sv) == "I");
  CHECK(escape_non_alnum("\x4A"sv) == "J");
  CHECK(escape_non_alnum("\x4B"sv) == "K");
  CHECK(escape_non_alnum("\x4C"sv) == "L");
  CHECK(escape_non_alnum("\x4D"sv) == "M");
  CHECK(escape_non_alnum("\x4E"sv) == "N");
  CHECK(escape_non_alnum("\x4F"sv) == "O");
  CHECK(escape_non_alnum("\x50"sv) == "P");
  CHECK(escape_non_alnum("\x51"sv) == "Q");
  CHECK(escape_non_alnum("\x52"sv) == "R");
  CHECK(escape_non_alnum("\x53"sv) == "S");
  CHECK(escape_non_alnum("\x54"sv) == "T");
  CHECK(escape_non_alnum("\x55"sv) == "U");
  CHECK(escape_non_alnum("\x56"sv) == "V");
  CHECK(escape_non_alnum("\x57"sv) == "W");
  CHECK(escape_non_alnum("\x58"sv) == "X");
  CHECK(escape_non_alnum("\x59"sv) == "Y");
  CHECK(escape_non_alnum("\x5A"sv) == "Z");
  CHECK(escape_non_alnum("\x5B"sv) == "_5b");
  CHECK(escape_non_alnum("\x5C"sv) == "_5c");
  CHECK(escape_non_alnum("\x5D"sv) == "_5d");
  CHECK(escape_non_alnum("\x5E"sv) == "_5e");
  CHECK(escape_non_alnum("\x5F"sv) == "__");
  CHECK(escape_non_alnum("\x60"sv) == "_60");
  CHECK(escape_non_alnum("\x61"sv) == "a");
  CHECK(escape_non_alnum("\x62"sv) == "b");
  CHECK(escape_non_alnum("\x63"sv) == "c");
  CHECK(escape_non_alnum("\x64"sv) == "d");
  CHECK(escape_non_alnum("\x65"sv) == "e");
  CHECK(escape_non_alnum("\x66"sv) == "f");
  CHECK(escape_non_alnum("\x67"sv) == "g");
  CHECK(escape_non_alnum("\x68"sv) == "h");
  CHECK(escape_non_alnum("\x69"sv) == "i");
  CHECK(escape_non_alnum("\x6A"sv) == "j");
  CHECK(escape_non_alnum("\x6B"sv) == "k");
  CHECK(escape_non_alnum("\x6C"sv) == "l");
  CHECK(escape_non_alnum("\x6D"sv) == "m");
  CHECK(escape_non_alnum("\x6E"sv) == "n");
  CHECK(escape_non_alnum("\x6F"sv) == "o");
  CHECK(escape_non_alnum("\x70"sv) == "p");
  CHECK(escape_non_alnum("\x71"sv) == "q");
  CHECK(escape_non_alnum("\x72"sv) == "r");
  CHECK(escape_non_alnum("\x73"sv) == "s");
  CHECK(escape_non_alnum("\x74"sv) == "t");
  CHECK(escape_non_alnum("\x75"sv) == "u");
  CHECK(escape_non_alnum("\x76"sv) == "v");
  CHECK(escape_non_alnum("\x77"sv) == "w");
  CHECK(escape_non_alnum("\x78"sv) == "x");
  CHECK(escape_non_alnum("\x79"sv) == "y");
  CHECK(escape_non_alnum("\x7A"sv) == "z");
  CHECK(escape_non_alnum("\x7B"sv) == "_7b");
  CHECK(escape_non_alnum("\x7C"sv) == "_7c");
  CHECK(escape_non_alnum("\x7D"sv) == "_7d");
  CHECK(escape_non_alnum("\x7E"sv) == "_7e");
  CHECK(escape_non_alnum("\x7F"sv) == "_7f");
}

TEST_CASE(
  "escape_non_alnum should work with any single byte character (part 2)",
  "[core][utils][string_utils][escape_non_alnum]")
{
  CHECK(escape_non_alnum("\x80"sv) == "_80");
  CHECK(escape_non_alnum("\x81"sv) == "_81");
  CHECK(escape_non_alnum("\x82"sv) == "_82");
  CHECK(escape_non_alnum("\x83"sv) == "_83");
  CHECK(escape_non_alnum("\x84"sv) == "_84");
  CHECK(escape_non_alnum("\x85"sv) == "_85");
  CHECK(escape_non_alnum("\x86"sv) == "_86");
  CHECK(escape_non_alnum("\x87"sv) == "_87");
  CHECK(escape_non_alnum("\x88"sv) == "_88");
  CHECK(escape_non_alnum("\x89"sv) == "_89");
  CHECK(escape_non_alnum("\x8A"sv) == "_8a");
  CHECK(escape_non_alnum("\x8B"sv) == "_8b");
  CHECK(escape_non_alnum("\x8C"sv) == "_8c");
  CHECK(escape_non_alnum("\x8D"sv) == "_8d");
  CHECK(escape_non_alnum("\x8E"sv) == "_8e");
  CHECK(escape_non_alnum("\x8F"sv) == "_8f");
  CHECK(escape_non_alnum("\x90"sv) == "_90");
  CHECK(escape_non_alnum("\x91"sv) == "_91");
  CHECK(escape_non_alnum("\x92"sv) == "_92");
  CHECK(escape_non_alnum("\x93"sv) == "_93");
  CHECK(escape_non_alnum("\x94"sv) == "_94");
  CHECK(escape_non_alnum("\x95"sv) == "_95");
  CHECK(escape_non_alnum("\x96"sv) == "_96");
  CHECK(escape_non_alnum("\x97"sv) == "_97");
  CHECK(escape_non_alnum("\x98"sv) == "_98");
  CHECK(escape_non_alnum("\x99"sv) == "_99");
  CHECK(escape_non_alnum("\x9A"sv) == "_9a");
  CHECK(escape_non_alnum("\x9B"sv) == "_9b");
  CHECK(escape_non_alnum("\x9C"sv) == "_9c");
  CHECK(escape_non_alnum("\x9D"sv) == "_9d");
  CHECK(escape_non_alnum("\x9E"sv) == "_9e");
  CHECK(escape_non_alnum("\x9F"sv) == "_9f");
  CHECK(escape_non_alnum("\xA0"sv) == "_a0");
  CHECK(escape_non_alnum("\xA1"sv) == "_a1");
  CHECK(escape_non_alnum("\xA2"sv) == "_a2");
  CHECK(escape_non_alnum("\xA3"sv) == "_a3");
  CHECK(escape_non_alnum("\xA4"sv) == "_a4");
  CHECK(escape_non_alnum("\xA5"sv) == "_a5");
  CHECK(escape_non_alnum("\xA6"sv) == "_a6");
  CHECK(escape_non_alnum("\xA7"sv) == "_a7");
  CHECK(escape_non_alnum("\xA8"sv) == "_a8");
  CHECK(escape_non_alnum("\xA9"sv) == "_a9");
  CHECK(escape_non_alnum("\xAA"sv) == "_aa");
  CHECK(escape_non_alnum("\xAB"sv) == "_ab");
  CHECK(escape_non_alnum("\xAC"sv) == "_ac");
  CHECK(escape_non_alnum("\xAD"sv) == "_ad");
  CHECK(escape_non_alnum("\xAE"sv) == "_ae");
  CHECK(escape_non_alnum("\xAF"sv) == "_af");
  CHECK(escape_non_alnum("\xB0"sv) == "_b0");
  CHECK(escape_non_alnum("\xB1"sv) == "_b1");
  CHECK(escape_non_alnum("\xB2"sv) == "_b2");
  CHECK(escape_non_alnum("\xB3"sv) == "_b3");
  CHECK(escape_non_alnum("\xB4"sv) == "_b4");
  CHECK(escape_non_alnum("\xB5"sv) == "_b5");
  CHECK(escape_non_alnum("\xB6"sv) == "_b6");
  CHECK(escape_non_alnum("\xB7"sv) == "_b7");
  CHECK(escape_non_alnum("\xB8"sv) == "_b8");
  CHECK(escape_non_alnum("\xB9"sv) == "_b9");
  CHECK(escape_non_alnum("\xBA"sv) == "_ba");
  CHECK(escape_non_alnum("\xBB"sv) == "_bb");
  CHECK(escape_non_alnum("\xBC"sv) == "_bc");
  CHECK(escape_non_alnum("\xBD"sv) == "_bd");
  CHECK(escape_non_alnum("\xBE"sv) == "_be");
  CHECK(escape_non_alnum("\xBF"sv) == "_bf");
  CHECK(escape_non_alnum("\xC0"sv) == "_c0");
  CHECK(escape_non_alnum("\xC1"sv) == "_c1");
  CHECK(escape_non_alnum("\xC2"sv) == "_c2");
  CHECK(escape_non_alnum("\xC3"sv) == "_c3");
  CHECK(escape_non_alnum("\xC4"sv) == "_c4");
  CHECK(escape_non_alnum("\xC5"sv) == "_c5");
  CHECK(escape_non_alnum("\xC6"sv) == "_c6");
  CHECK(escape_non_alnum("\xC7"sv) == "_c7");
  CHECK(escape_non_alnum("\xC8"sv) == "_c8");
  CHECK(escape_non_alnum("\xC9"sv) == "_c9");
  CHECK(escape_non_alnum("\xCA"sv) == "_ca");
  CHECK(escape_non_alnum("\xCB"sv) == "_cb");
  CHECK(escape_non_alnum("\xCC"sv) == "_cc");
  CHECK(escape_non_alnum("\xCD"sv) == "_cd");
  CHECK(escape_non_alnum("\xCE"sv) == "_ce");
  CHECK(escape_non_alnum("\xCF"sv) == "_cf");
  CHECK(escape_non_alnum("\xD0"sv) == "_d0");
  CHECK(escape_non_alnum("\xD1"sv) == "_d1");
  CHECK(escape_non_alnum("\xD2"sv) == "_d2");
  CHECK(escape_non_alnum("\xD3"sv) == "_d3");
  CHECK(escape_non_alnum("\xD4"sv) == "_d4");
  CHECK(escape_non_alnum("\xD5"sv) == "_d5");
  CHECK(escape_non_alnum("\xD6"sv) == "_d6");
  CHECK(escape_non_alnum("\xD7"sv) == "_d7");
  CHECK(escape_non_alnum("\xD8"sv) == "_d8");
  CHECK(escape_non_alnum("\xD9"sv) == "_d9");
  CHECK(escape_non_alnum("\xDA"sv) == "_da");
  CHECK(escape_non_alnum("\xDB"sv) == "_db");
  CHECK(escape_non_alnum("\xDC"sv) == "_dc");
  CHECK(escape_non_alnum("\xDD"sv) == "_dd");
  CHECK(escape_non_alnum("\xDE"sv) == "_de");
  CHECK(escape_non_alnum("\xDF"sv) == "_df");
  CHECK(escape_non_alnum("\xE0"sv) == "_e0");
  CHECK(escape_non_alnum("\xE1"sv) == "_e1");
  CHECK(escape_non_alnum("\xE2"sv) == "_e2");
  CHECK(escape_non_alnum("\xE3"sv) == "_e3");
  CHECK(escape_non_alnum("\xE4"sv) == "_e4");
  CHECK(escape_non_alnum("\xE5"sv) == "_e5");
  CHECK(escape_non_alnum("\xE6"sv) == "_e6");
  CHECK(escape_non_alnum("\xE7"sv) == "_e7");
  CHECK(escape_non_alnum("\xE8"sv) == "_e8");
  CHECK(escape_non_alnum("\xE9"sv) == "_e9");
  CHECK(escape_non_alnum("\xEA"sv) == "_ea");
  CHECK(escape_non_alnum("\xEB"sv) == "_eb");
  CHECK(escape_non_alnum("\xEC"sv) == "_ec");
  CHECK(escape_non_alnum("\xED"sv) == "_ed");
  CHECK(escape_non_alnum("\xEE"sv) == "_ee");
  CHECK(escape_non_alnum("\xEF"sv) == "_ef");
  CHECK(escape_non_alnum("\xF0"sv) == "_f0");
  CHECK(escape_non_alnum("\xF1"sv) == "_f1");
  CHECK(escape_non_alnum("\xF2"sv) == "_f2");
  CHECK(escape_non_alnum("\xF3"sv) == "_f3");
  CHECK(escape_non_alnum("\xF4"sv) == "_f4");
  CHECK(escape_non_alnum("\xF5"sv) == "_f5");
  CHECK(escape_non_alnum("\xF6"sv) == "_f6");
  CHECK(escape_non_alnum("\xF7"sv) == "_f7");
  CHECK(escape_non_alnum("\xF8"sv) == "_f8");
  CHECK(escape_non_alnum("\xF9"sv) == "_f9");
  CHECK(escape_non_alnum("\xFA"sv) == "_fa");
  CHECK(escape_non_alnum("\xFB"sv) == "_fb");
  CHECK(escape_non_alnum("\xFC"sv) == "_fc");
  CHECK(escape_non_alnum("\xFD"sv) == "_fd");
  CHECK(escape_non_alnum("\xFE"sv) == "_fe");
  CHECK(escape_non_alnum("\xFF"sv) == "_ff");
}

TEST_CASE(
  "escape_non_alnum honours string_view length over a non-NUL-terminated "
  "buffer",
  "[core][utils][string_utils][escape_non_alnum]")
{
  // Without a trailing NUL: a regression where the implementation
  // walked the buffer until '\0' would read past the end.
  const char buf[] = {'a', '_', 'X', 'Y'};
  std::string_view sv{buf, 2};
  REQUIRE(escape_non_alnum(sv) == "a__");
}
