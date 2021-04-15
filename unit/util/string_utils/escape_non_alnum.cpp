/*******************************************************************\

Module: Unit tests of escape_non_alnum

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// escape_non_alnum Unit Tests

#include <testing-utils/use_catch.h>
#include <util/string_utils.h>

#include <string>

// test split into two halves to avoid a GCC warning ("variable tracking size
// limit exceeded with -fvar-tracking-assignments, retrying without")
TEST_CASE(
  "escape_non_alnum should work with any single byte character (part 1)",
  "[core][utils][string_utils][escape_non_alnum]")
{
  CHECK(escape_non_alnum({'\x00'}) == "_00");
  CHECK(escape_non_alnum({'\x01'}) == "_01");
  CHECK(escape_non_alnum({'\x02'}) == "_02");
  CHECK(escape_non_alnum({'\x03'}) == "_03");
  CHECK(escape_non_alnum({'\x04'}) == "_04");
  CHECK(escape_non_alnum({'\x05'}) == "_05");
  CHECK(escape_non_alnum({'\x06'}) == "_06");
  CHECK(escape_non_alnum({'\x07'}) == "_07");
  CHECK(escape_non_alnum({'\x08'}) == "_08");
  CHECK(escape_non_alnum({'\x09'}) == "_09");
  CHECK(escape_non_alnum({'\x0A'}) == "_0a");
  CHECK(escape_non_alnum({'\x0B'}) == "_0b");
  CHECK(escape_non_alnum({'\x0C'}) == "_0c");
  CHECK(escape_non_alnum({'\x0D'}) == "_0d");
  CHECK(escape_non_alnum({'\x0E'}) == "_0e");
  CHECK(escape_non_alnum({'\x0F'}) == "_0f");
  CHECK(escape_non_alnum({'\x10'}) == "_10");
  CHECK(escape_non_alnum({'\x11'}) == "_11");
  CHECK(escape_non_alnum({'\x12'}) == "_12");
  CHECK(escape_non_alnum({'\x13'}) == "_13");
  CHECK(escape_non_alnum({'\x14'}) == "_14");
  CHECK(escape_non_alnum({'\x15'}) == "_15");
  CHECK(escape_non_alnum({'\x16'}) == "_16");
  CHECK(escape_non_alnum({'\x17'}) == "_17");
  CHECK(escape_non_alnum({'\x18'}) == "_18");
  CHECK(escape_non_alnum({'\x19'}) == "_19");
  CHECK(escape_non_alnum({'\x1A'}) == "_1a");
  CHECK(escape_non_alnum({'\x1B'}) == "_1b");
  CHECK(escape_non_alnum({'\x1C'}) == "_1c");
  CHECK(escape_non_alnum({'\x1D'}) == "_1d");
  CHECK(escape_non_alnum({'\x1E'}) == "_1e");
  CHECK(escape_non_alnum({'\x1F'}) == "_1f");
  CHECK(escape_non_alnum({'\x20'}) == "_20");
  CHECK(escape_non_alnum({'\x21'}) == "_21");
  CHECK(escape_non_alnum({'\x22'}) == "_22");
  CHECK(escape_non_alnum({'\x23'}) == "_23");
  CHECK(escape_non_alnum({'\x24'}) == "_24");
  CHECK(escape_non_alnum({'\x25'}) == "_25");
  CHECK(escape_non_alnum({'\x26'}) == "_26");
  CHECK(escape_non_alnum({'\x27'}) == "_27");
  CHECK(escape_non_alnum({'\x28'}) == "_28");
  CHECK(escape_non_alnum({'\x29'}) == "_29");
  CHECK(escape_non_alnum({'\x2A'}) == "_2a");
  CHECK(escape_non_alnum({'\x2B'}) == "_2b");
  CHECK(escape_non_alnum({'\x2B'}) == "_2b");
  CHECK(escape_non_alnum({'\x2C'}) == "_2c");
  CHECK(escape_non_alnum({'\x2D'}) == "_2d");
  CHECK(escape_non_alnum({'\x2E'}) == "_2e");
  CHECK(escape_non_alnum({'\x2F'}) == "_2f");
  CHECK(escape_non_alnum({'\x30'}) == "0");
  CHECK(escape_non_alnum({'\x31'}) == "1");
  CHECK(escape_non_alnum({'\x32'}) == "2");
  CHECK(escape_non_alnum({'\x33'}) == "3");
  CHECK(escape_non_alnum({'\x34'}) == "4");
  CHECK(escape_non_alnum({'\x35'}) == "5");
  CHECK(escape_non_alnum({'\x36'}) == "6");
  CHECK(escape_non_alnum({'\x37'}) == "7");
  CHECK(escape_non_alnum({'\x38'}) == "8");
  CHECK(escape_non_alnum({'\x39'}) == "9");
  CHECK(escape_non_alnum({'\x3A'}) == "_3a");
  CHECK(escape_non_alnum({'\x3B'}) == "_3b");
  CHECK(escape_non_alnum({'\x3C'}) == "_3c");
  CHECK(escape_non_alnum({'\x3D'}) == "_3d");
  CHECK(escape_non_alnum({'\x3E'}) == "_3e");
  CHECK(escape_non_alnum({'\x3F'}) == "_3f");
  CHECK(escape_non_alnum({'\x40'}) == "_40");
  CHECK(escape_non_alnum({'\x41'}) == "A");
  CHECK(escape_non_alnum({'\x42'}) == "B");
  CHECK(escape_non_alnum({'\x43'}) == "C");
  CHECK(escape_non_alnum({'\x44'}) == "D");
  CHECK(escape_non_alnum({'\x45'}) == "E");
  CHECK(escape_non_alnum({'\x46'}) == "F");
  CHECK(escape_non_alnum({'\x47'}) == "G");
  CHECK(escape_non_alnum({'\x48'}) == "H");
  CHECK(escape_non_alnum({'\x49'}) == "I");
  CHECK(escape_non_alnum({'\x4A'}) == "J");
  CHECK(escape_non_alnum({'\x4B'}) == "K");
  CHECK(escape_non_alnum({'\x4C'}) == "L");
  CHECK(escape_non_alnum({'\x4D'}) == "M");
  CHECK(escape_non_alnum({'\x4E'}) == "N");
  CHECK(escape_non_alnum({'\x4F'}) == "O");
  CHECK(escape_non_alnum({'\x50'}) == "P");
  CHECK(escape_non_alnum({'\x51'}) == "Q");
  CHECK(escape_non_alnum({'\x52'}) == "R");
  CHECK(escape_non_alnum({'\x53'}) == "S");
  CHECK(escape_non_alnum({'\x54'}) == "T");
  CHECK(escape_non_alnum({'\x55'}) == "U");
  CHECK(escape_non_alnum({'\x56'}) == "V");
  CHECK(escape_non_alnum({'\x57'}) == "W");
  CHECK(escape_non_alnum({'\x58'}) == "X");
  CHECK(escape_non_alnum({'\x59'}) == "Y");
  CHECK(escape_non_alnum({'\x5A'}) == "Z");
  CHECK(escape_non_alnum({'\x5B'}) == "_5b");
  CHECK(escape_non_alnum({'\x5C'}) == "_5c");
  CHECK(escape_non_alnum({'\x5D'}) == "_5d");
  CHECK(escape_non_alnum({'\x5E'}) == "_5e");
  CHECK(escape_non_alnum({'\x5F'}) == "__");
  CHECK(escape_non_alnum({'\x60'}) == "_60");
  CHECK(escape_non_alnum({'\x61'}) == "a");
  CHECK(escape_non_alnum({'\x62'}) == "b");
  CHECK(escape_non_alnum({'\x63'}) == "c");
  CHECK(escape_non_alnum({'\x64'}) == "d");
  CHECK(escape_non_alnum({'\x65'}) == "e");
  CHECK(escape_non_alnum({'\x66'}) == "f");
  CHECK(escape_non_alnum({'\x67'}) == "g");
  CHECK(escape_non_alnum({'\x68'}) == "h");
  CHECK(escape_non_alnum({'\x69'}) == "i");
  CHECK(escape_non_alnum({'\x6A'}) == "j");
  CHECK(escape_non_alnum({'\x6B'}) == "k");
  CHECK(escape_non_alnum({'\x6C'}) == "l");
  CHECK(escape_non_alnum({'\x6D'}) == "m");
  CHECK(escape_non_alnum({'\x6E'}) == "n");
  CHECK(escape_non_alnum({'\x6F'}) == "o");
  CHECK(escape_non_alnum({'\x70'}) == "p");
  CHECK(escape_non_alnum({'\x71'}) == "q");
  CHECK(escape_non_alnum({'\x72'}) == "r");
  CHECK(escape_non_alnum({'\x73'}) == "s");
  CHECK(escape_non_alnum({'\x74'}) == "t");
  CHECK(escape_non_alnum({'\x75'}) == "u");
  CHECK(escape_non_alnum({'\x76'}) == "v");
  CHECK(escape_non_alnum({'\x77'}) == "w");
  CHECK(escape_non_alnum({'\x78'}) == "x");
  CHECK(escape_non_alnum({'\x79'}) == "y");
  CHECK(escape_non_alnum({'\x7A'}) == "z");
  CHECK(escape_non_alnum({'\x7B'}) == "_7b");
  CHECK(escape_non_alnum({'\x7C'}) == "_7c");
  CHECK(escape_non_alnum({'\x7D'}) == "_7d");
  CHECK(escape_non_alnum({'\x7E'}) == "_7e");
  CHECK(escape_non_alnum({'\x7F'}) == "_7f");
}

TEST_CASE(
  "escape_non_alnum should work with any single byte character (part 2)",
  "[core][utils][string_utils][escape_non_alnum]")
{
  CHECK(escape_non_alnum({'\x80'}) == "_80");
  CHECK(escape_non_alnum({'\x81'}) == "_81");
  CHECK(escape_non_alnum({'\x82'}) == "_82");
  CHECK(escape_non_alnum({'\x83'}) == "_83");
  CHECK(escape_non_alnum({'\x84'}) == "_84");
  CHECK(escape_non_alnum({'\x85'}) == "_85");
  CHECK(escape_non_alnum({'\x86'}) == "_86");
  CHECK(escape_non_alnum({'\x87'}) == "_87");
  CHECK(escape_non_alnum({'\x88'}) == "_88");
  CHECK(escape_non_alnum({'\x89'}) == "_89");
  CHECK(escape_non_alnum({'\x8A'}) == "_8a");
  CHECK(escape_non_alnum({'\x8B'}) == "_8b");
  CHECK(escape_non_alnum({'\x8C'}) == "_8c");
  CHECK(escape_non_alnum({'\x8D'}) == "_8d");
  CHECK(escape_non_alnum({'\x8E'}) == "_8e");
  CHECK(escape_non_alnum({'\x8F'}) == "_8f");
  CHECK(escape_non_alnum({'\x90'}) == "_90");
  CHECK(escape_non_alnum({'\x91'}) == "_91");
  CHECK(escape_non_alnum({'\x92'}) == "_92");
  CHECK(escape_non_alnum({'\x93'}) == "_93");
  CHECK(escape_non_alnum({'\x94'}) == "_94");
  CHECK(escape_non_alnum({'\x95'}) == "_95");
  CHECK(escape_non_alnum({'\x96'}) == "_96");
  CHECK(escape_non_alnum({'\x97'}) == "_97");
  CHECK(escape_non_alnum({'\x98'}) == "_98");
  CHECK(escape_non_alnum({'\x99'}) == "_99");
  CHECK(escape_non_alnum({'\x9A'}) == "_9a");
  CHECK(escape_non_alnum({'\x9B'}) == "_9b");
  CHECK(escape_non_alnum({'\x9C'}) == "_9c");
  CHECK(escape_non_alnum({'\x9D'}) == "_9d");
  CHECK(escape_non_alnum({'\x9E'}) == "_9e");
  CHECK(escape_non_alnum({'\x9F'}) == "_9f");
  CHECK(escape_non_alnum({'\xA0'}) == "_a0");
  CHECK(escape_non_alnum({'\xA1'}) == "_a1");
  CHECK(escape_non_alnum({'\xA2'}) == "_a2");
  CHECK(escape_non_alnum({'\xA3'}) == "_a3");
  CHECK(escape_non_alnum({'\xA4'}) == "_a4");
  CHECK(escape_non_alnum({'\xA5'}) == "_a5");
  CHECK(escape_non_alnum({'\xA6'}) == "_a6");
  CHECK(escape_non_alnum({'\xA7'}) == "_a7");
  CHECK(escape_non_alnum({'\xA8'}) == "_a8");
  CHECK(escape_non_alnum({'\xA9'}) == "_a9");
  CHECK(escape_non_alnum({'\xAA'}) == "_aa");
  CHECK(escape_non_alnum({'\xAB'}) == "_ab");
  CHECK(escape_non_alnum({'\xAC'}) == "_ac");
  CHECK(escape_non_alnum({'\xAD'}) == "_ad");
  CHECK(escape_non_alnum({'\xAE'}) == "_ae");
  CHECK(escape_non_alnum({'\xAF'}) == "_af");
  CHECK(escape_non_alnum({'\xB0'}) == "_b0");
  CHECK(escape_non_alnum({'\xB1'}) == "_b1");
  CHECK(escape_non_alnum({'\xB2'}) == "_b2");
  CHECK(escape_non_alnum({'\xB3'}) == "_b3");
  CHECK(escape_non_alnum({'\xB4'}) == "_b4");
  CHECK(escape_non_alnum({'\xB5'}) == "_b5");
  CHECK(escape_non_alnum({'\xB6'}) == "_b6");
  CHECK(escape_non_alnum({'\xB7'}) == "_b7");
  CHECK(escape_non_alnum({'\xB8'}) == "_b8");
  CHECK(escape_non_alnum({'\xB9'}) == "_b9");
  CHECK(escape_non_alnum({'\xBA'}) == "_ba");
  CHECK(escape_non_alnum({'\xBB'}) == "_bb");
  CHECK(escape_non_alnum({'\xBC'}) == "_bc");
  CHECK(escape_non_alnum({'\xBD'}) == "_bd");
  CHECK(escape_non_alnum({'\xBE'}) == "_be");
  CHECK(escape_non_alnum({'\xBF'}) == "_bf");
  CHECK(escape_non_alnum({'\xC0'}) == "_c0");
  CHECK(escape_non_alnum({'\xC1'}) == "_c1");
  CHECK(escape_non_alnum({'\xC2'}) == "_c2");
  CHECK(escape_non_alnum({'\xC3'}) == "_c3");
  CHECK(escape_non_alnum({'\xC4'}) == "_c4");
  CHECK(escape_non_alnum({'\xC5'}) == "_c5");
  CHECK(escape_non_alnum({'\xC6'}) == "_c6");
  CHECK(escape_non_alnum({'\xC7'}) == "_c7");
  CHECK(escape_non_alnum({'\xC8'}) == "_c8");
  CHECK(escape_non_alnum({'\xC9'}) == "_c9");
  CHECK(escape_non_alnum({'\xCA'}) == "_ca");
  CHECK(escape_non_alnum({'\xCB'}) == "_cb");
  CHECK(escape_non_alnum({'\xCC'}) == "_cc");
  CHECK(escape_non_alnum({'\xCD'}) == "_cd");
  CHECK(escape_non_alnum({'\xCE'}) == "_ce");
  CHECK(escape_non_alnum({'\xCF'}) == "_cf");
  CHECK(escape_non_alnum({'\xD0'}) == "_d0");
  CHECK(escape_non_alnum({'\xD1'}) == "_d1");
  CHECK(escape_non_alnum({'\xD2'}) == "_d2");
  CHECK(escape_non_alnum({'\xD3'}) == "_d3");
  CHECK(escape_non_alnum({'\xD4'}) == "_d4");
  CHECK(escape_non_alnum({'\xD5'}) == "_d5");
  CHECK(escape_non_alnum({'\xD6'}) == "_d6");
  CHECK(escape_non_alnum({'\xD7'}) == "_d7");
  CHECK(escape_non_alnum({'\xD8'}) == "_d8");
  CHECK(escape_non_alnum({'\xD9'}) == "_d9");
  CHECK(escape_non_alnum({'\xDA'}) == "_da");
  CHECK(escape_non_alnum({'\xDB'}) == "_db");
  CHECK(escape_non_alnum({'\xDC'}) == "_dc");
  CHECK(escape_non_alnum({'\xDD'}) == "_dd");
  CHECK(escape_non_alnum({'\xDE'}) == "_de");
  CHECK(escape_non_alnum({'\xDF'}) == "_df");
  CHECK(escape_non_alnum({'\xE0'}) == "_e0");
  CHECK(escape_non_alnum({'\xE1'}) == "_e1");
  CHECK(escape_non_alnum({'\xE2'}) == "_e2");
  CHECK(escape_non_alnum({'\xE3'}) == "_e3");
  CHECK(escape_non_alnum({'\xE4'}) == "_e4");
  CHECK(escape_non_alnum({'\xE5'}) == "_e5");
  CHECK(escape_non_alnum({'\xE6'}) == "_e6");
  CHECK(escape_non_alnum({'\xE7'}) == "_e7");
  CHECK(escape_non_alnum({'\xE8'}) == "_e8");
  CHECK(escape_non_alnum({'\xE9'}) == "_e9");
  CHECK(escape_non_alnum({'\xEA'}) == "_ea");
  CHECK(escape_non_alnum({'\xEB'}) == "_eb");
  CHECK(escape_non_alnum({'\xEC'}) == "_ec");
  CHECK(escape_non_alnum({'\xED'}) == "_ed");
  CHECK(escape_non_alnum({'\xEE'}) == "_ee");
  CHECK(escape_non_alnum({'\xEF'}) == "_ef");
  CHECK(escape_non_alnum({'\xF0'}) == "_f0");
  CHECK(escape_non_alnum({'\xF1'}) == "_f1");
  CHECK(escape_non_alnum({'\xF2'}) == "_f2");
  CHECK(escape_non_alnum({'\xF3'}) == "_f3");
  CHECK(escape_non_alnum({'\xF4'}) == "_f4");
  CHECK(escape_non_alnum({'\xF5'}) == "_f5");
  CHECK(escape_non_alnum({'\xF6'}) == "_f6");
  CHECK(escape_non_alnum({'\xF7'}) == "_f7");
  CHECK(escape_non_alnum({'\xF8'}) == "_f8");
  CHECK(escape_non_alnum({'\xF9'}) == "_f9");
  CHECK(escape_non_alnum({'\xFA'}) == "_fa");
  CHECK(escape_non_alnum({'\xFB'}) == "_fb");
  CHECK(escape_non_alnum({'\xFC'}) == "_fc");
  CHECK(escape_non_alnum({'\xFD'}) == "_fd");
  CHECK(escape_non_alnum({'\xFE'}) == "_fe");
  CHECK(escape_non_alnum({'\xFF'}) == "_ff");
}
