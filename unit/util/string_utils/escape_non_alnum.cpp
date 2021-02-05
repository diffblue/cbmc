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
  "escape_non_alnum should work with any single byte signed character (part 1)",
  "[core][utils][string_utils][escape_non_alnum]")
{
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x00)}) == "_00");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x01)}) == "_01");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x02)}) == "_02");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x03)}) == "_03");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x04)}) == "_04");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x05)}) == "_05");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x06)}) == "_06");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x07)}) == "_07");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x08)}) == "_08");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x09)}) == "_09");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x0A)}) == "_0a");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x0B)}) == "_0b");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x0C)}) == "_0c");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x0D)}) == "_0d");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x0E)}) == "_0e");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x0F)}) == "_0f");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x10)}) == "_10");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x11)}) == "_11");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x12)}) == "_12");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x13)}) == "_13");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x14)}) == "_14");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x15)}) == "_15");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x16)}) == "_16");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x17)}) == "_17");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x18)}) == "_18");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x19)}) == "_19");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x1A)}) == "_1a");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x1B)}) == "_1b");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x1C)}) == "_1c");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x1D)}) == "_1d");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x1E)}) == "_1e");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x1F)}) == "_1f");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x20)}) == "_20");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x21)}) == "_21");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x22)}) == "_22");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x23)}) == "_23");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x24)}) == "_24");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x25)}) == "_25");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x26)}) == "_26");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x27)}) == "_27");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x28)}) == "_28");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x29)}) == "_29");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x2A)}) == "_2a");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x2B)}) == "_2b");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x2B)}) == "_2b");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x2C)}) == "_2c");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x2D)}) == "_2d");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x2E)}) == "_2e");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x2F)}) == "_2f");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x30)}) == "0");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x31)}) == "1");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x32)}) == "2");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x33)}) == "3");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x34)}) == "4");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x35)}) == "5");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x36)}) == "6");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x37)}) == "7");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x38)}) == "8");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x39)}) == "9");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x3A)}) == "_3a");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x3B)}) == "_3b");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x3C)}) == "_3c");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x3D)}) == "_3d");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x3E)}) == "_3e");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x3F)}) == "_3f");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x40)}) == "_40");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x41)}) == "A");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x42)}) == "B");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x43)}) == "C");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x44)}) == "D");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x45)}) == "E");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x46)}) == "F");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x47)}) == "G");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x48)}) == "H");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x49)}) == "I");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x4A)}) == "J");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x4B)}) == "K");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x4C)}) == "L");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x4D)}) == "M");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x4E)}) == "N");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x4F)}) == "O");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x50)}) == "P");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x51)}) == "Q");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x52)}) == "R");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x53)}) == "S");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x54)}) == "T");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x55)}) == "U");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x56)}) == "V");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x57)}) == "W");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x58)}) == "X");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x59)}) == "Y");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x5A)}) == "Z");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x5B)}) == "_5b");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x5C)}) == "_5c");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x5D)}) == "_5d");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x5E)}) == "_5e");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x5F)}) == "__");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x60)}) == "_60");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x61)}) == "a");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x62)}) == "b");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x63)}) == "c");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x64)}) == "d");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x65)}) == "e");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x66)}) == "f");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x67)}) == "g");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x68)}) == "h");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x69)}) == "i");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x6A)}) == "j");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x6B)}) == "k");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x6C)}) == "l");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x6D)}) == "m");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x6E)}) == "n");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x6F)}) == "o");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x70)}) == "p");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x71)}) == "q");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x72)}) == "r");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x73)}) == "s");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x74)}) == "t");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x75)}) == "u");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x76)}) == "v");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x77)}) == "w");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x78)}) == "x");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x79)}) == "y");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x7A)}) == "z");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x7B)}) == "_7b");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x7C)}) == "_7c");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x7D)}) == "_7d");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x7E)}) == "_7e");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x7F)}) == "_7f");
}

TEST_CASE(
  "escape_non_alnum should work with any single byte signed character (part 2)",
  "[core][utils][string_utils][escape_non_alnum]")
{
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x80)}) == "_80");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x81)}) == "_81");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x82)}) == "_82");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x83)}) == "_83");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x84)}) == "_84");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x85)}) == "_85");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x86)}) == "_86");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x87)}) == "_87");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x88)}) == "_88");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x89)}) == "_89");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x8A)}) == "_8a");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x8B)}) == "_8b");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x8C)}) == "_8c");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x8D)}) == "_8d");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x8E)}) == "_8e");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x8F)}) == "_8f");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x90)}) == "_90");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x91)}) == "_91");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x92)}) == "_92");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x93)}) == "_93");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x94)}) == "_94");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x95)}) == "_95");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x96)}) == "_96");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x97)}) == "_97");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x98)}) == "_98");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x99)}) == "_99");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x9A)}) == "_9a");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x9B)}) == "_9b");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x9C)}) == "_9c");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x9D)}) == "_9d");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x9E)}) == "_9e");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0x9F)}) == "_9f");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xA0)}) == "_a0");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xA1)}) == "_a1");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xA2)}) == "_a2");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xA3)}) == "_a3");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xA4)}) == "_a4");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xA5)}) == "_a5");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xA6)}) == "_a6");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xA7)}) == "_a7");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xA8)}) == "_a8");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xA9)}) == "_a9");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xAA)}) == "_aa");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xAB)}) == "_ab");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xAC)}) == "_ac");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xAD)}) == "_ad");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xAE)}) == "_ae");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xAF)}) == "_af");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xB0)}) == "_b0");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xB1)}) == "_b1");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xB2)}) == "_b2");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xB3)}) == "_b3");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xB4)}) == "_b4");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xB5)}) == "_b5");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xB6)}) == "_b6");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xB7)}) == "_b7");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xB8)}) == "_b8");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xB9)}) == "_b9");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xBA)}) == "_ba");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xBB)}) == "_bb");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xBC)}) == "_bc");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xBD)}) == "_bd");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xBE)}) == "_be");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xBF)}) == "_bf");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xC0)}) == "_c0");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xC1)}) == "_c1");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xC2)}) == "_c2");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xC3)}) == "_c3");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xC4)}) == "_c4");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xC5)}) == "_c5");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xC6)}) == "_c6");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xC7)}) == "_c7");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xC8)}) == "_c8");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xC9)}) == "_c9");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xCA)}) == "_ca");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xCB)}) == "_cb");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xCC)}) == "_cc");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xCD)}) == "_cd");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xCE)}) == "_ce");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xCF)}) == "_cf");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xD0)}) == "_d0");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xD1)}) == "_d1");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xD2)}) == "_d2");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xD3)}) == "_d3");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xD4)}) == "_d4");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xD5)}) == "_d5");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xD6)}) == "_d6");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xD7)}) == "_d7");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xD8)}) == "_d8");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xD9)}) == "_d9");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xDA)}) == "_da");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xDB)}) == "_db");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xDC)}) == "_dc");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xDD)}) == "_dd");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xDE)}) == "_de");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xDF)}) == "_df");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xE0)}) == "_e0");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xE1)}) == "_e1");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xE2)}) == "_e2");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xE3)}) == "_e3");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xE4)}) == "_e4");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xE5)}) == "_e5");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xE6)}) == "_e6");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xE7)}) == "_e7");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xE8)}) == "_e8");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xE9)}) == "_e9");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xEA)}) == "_ea");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xEB)}) == "_eb");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xEC)}) == "_ec");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xED)}) == "_ed");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xEE)}) == "_ee");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xEF)}) == "_ef");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xF0)}) == "_f0");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xF1)}) == "_f1");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xF2)}) == "_f2");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xF3)}) == "_f3");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xF4)}) == "_f4");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xF5)}) == "_f5");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xF6)}) == "_f6");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xF7)}) == "_f7");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xF8)}) == "_f8");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xF9)}) == "_f9");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xFA)}) == "_fa");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xFB)}) == "_fb");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xFC)}) == "_fc");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xFD)}) == "_fd");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xFE)}) == "_fe");
  CHECK(escape_non_alnum(std::string{static_cast<signed char>(0xFF)}) == "_ff");
}
