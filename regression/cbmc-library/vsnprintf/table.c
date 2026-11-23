#include <assert.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

// Each case formats into b, a large buffer, and into t, one of 6 characters,
// and compares the output and the result with those of glibc.
#define CHECK(expected, expected_truncated, expected_result, ...)              \
  do                                                                           \
  {                                                                            \
    int r = snprintf(b, sizeof b, __VA_ARGS__);                                \
    assert(r == (expected_result) && strcmp(b, (expected)) == 0);              \
    r = snprintf(t, sizeof t, __VA_ARGS__);                                    \
    assert(r == (expected_result) && strcmp(t, (expected_truncated)) == 0);    \
  } while(0)

int main()
{
  char b[64];
  char t[6];
  CHECK("-2147483648", "-2147", 11, "%d", -2147483647 - 1);
  CHECK("2147483647", "21474", 10, "%d", 2147483647);
  CHECK("4294967295", "42949", 10, "%u", 4294967295u);
  CHECK(
    "-9223372036854775808", "-9223", 20, "%lld", -9223372036854775807ll - 1);
  CHECK("18446744073709551615", "18446", 20, "%llu", 18446744073709551615ull);
  CHECK("ffffffffffffffff", "fffff", 16, "%llx", 18446744073709551615ull);
  CHECK("1777777777777777777777", "17777", 22, "%llo", 18446744073709551615ull);
  CHECK(" 42", " 42", 3, "% d", 42);
  CHECK("+5", "+5", 2, "%+ d", 5);
  CHECK("+0", "+0", 2, "%+d", 0);
  CHECK("-0042", "-0042", 5, "%05d", -42);
  CHECK("42   |", "42   ", 6, "%-5d|", 42);
  CHECK("42   |", "42   ", 6, "%-05d|", 42);
  CHECK("     042|", "     ", 9, "%08.3d|", 42);
  CHECK("   42|", "   42", 6, "%*d|", 5, 42);
  CHECK("42   |", "42   ", 6, "%*d|", -5, 42);
  CHECK("007", "007", 3, "%.*d", 3, 7);
  CHECK("7", "7", 1, "%.*d", -1, 7);
  CHECK("44", "44", 2, "%hhd", 300);
  CHECK("44", "44", 2, "%hhu", 300);
  CHECK("127", "127", 3, "%hhd", -129);
  CHECK("4464", "4464", 4, "%hd", 70000);
  CHECK("4464", "4464", 4, "%hu", 70000);
  CHECK("-2147483648", "-2147", 11, "%ld", -2147483647l - 1);
  CHECK("4294967295", "42949", 10, "%lu", 4294967295ul);
  CHECK(
    "-9223372036854775808",
    "-9223",
    20,
    "%jd",
    (intmax_t)(-9223372036854775807ll - 1));
  CHECK(
    "18446744073709551615",
    "18446",
    20,
    "%ju",
    (uintmax_t)18446744073709551615ull);
  CHECK("123456", "12345", 6, "%zu", (size_t)123456);
  CHECK("beef", "beef", 4, "%zx", (size_t)48879);
  CHECK("-123456", "-1234", 7, "%td", (ptrdiff_t)-123456);
  CHECK("  abc|", "  abc", 6, "%5.3s|", "abcdef");
  CHECK("ab    |", "ab   ", 7, "%-6s|", "ab");
  CHECK("|", "|", 1, "%.0s|", "ab");
  CHECK("x   |", "x   |", 5, "%-4c|", 'x');
  CHECK("  y|", "  y|", 4, "%3c|", 'y');
  CHECK("|", "|", 1, "%.0d|", 0);
  CHECK("     |", "     ", 6, "%5.0d|", 0);
  CHECK("0|", "0|", 2, "%#.0o|", 0);
  CHECK("0", "0", 1, "%#o", 0);
  CHECK("010", "010", 3, "%#o", 8);
  CHECK("0", "0", 1, "%#x", 0);
  CHECK("0xff", "0xff", 4, "%#x", 255);
  CHECK("0XFF", "0XFF", 4, "%#X", 255);
  CHECK("0x0000ff", "0x000", 8, "%#08x", 255);
  CHECK("0010", "0010", 4, "%#.4o", 8);
  CHECK("777 beef BEEF", "777 b", 13, "%o %x %X", 511, 48879, 48879);
  CHECK("-17", "-17", 3, "%i", -17);
  CHECK("%|abc1", "%|abc", 6, "%%|%c%s%d", 'a', "bc", 1);
  return 0;
}
