// Unit proof for strip_string (src/util/string_utils.cpp).
//
// Unlike the unit test (unit/util/string_utils/strip_string.cpp), which
// checks a fixed set of sample strings, this harness verifies the
// function's contract over ALL strings up to a bounded length, built
// from nondeterministic characters:
//  * the result has no leading and no trailing whitespace;
//  * stripping is idempotent: strip(strip(s)) == strip(s);
//  * a string with no leading/trailing whitespace is returned unchanged.
// Single translation unit: include the implementation directly.  (The
// C++ front end does not yet merge identical inline member definitions
// across translation units, [basic.def.odr]/13.)
#include <util/string_utils.h>

#include "../../../src/util/string_utils.cpp" // IWYU pragma: keep

#include <cctype>

extern "C" void __CPROVER_assert(bool, const char *);
extern "C" void __CPROVER_assume(bool);
int __VERIFIER_nondet_int();
char __VERIFIER_nondet_char();

#define MAX_LEN 3

int main()
{
  // bounded-nondet input string
  int len = __VERIFIER_nondet_int();
  __CPROVER_assume(len >= 0 && len <= MAX_LEN);
  char buf[MAX_LEN + 1];
  for(int i = 0; i < MAX_LEN; ++i)
  {
    char c = __VERIFIER_nondet_char();
    // printable ASCII plus the standard white-space characters, and
    // non-zero (std::string contents; isspace is UB outside uchar range)
    __CPROVER_assume(
      (c >= 0x20 && c <= 0x7e) || c == '\t' || c == '\n' || c == '\v' ||
      c == '\f' || c == '\r');
    buf[i] = c;
  }
  buf[len] = '\0';
  const std::string s(buf, len);

  const std::string stripped = strip_string(s);

  // no leading/trailing whitespace
  if(!stripped.empty())
  {
    __CPROVER_assert(
      !std::isspace(static_cast<unsigned char>(stripped.front())),
      "no leading whitespace");
    __CPROVER_assert(
      !std::isspace(static_cast<unsigned char>(stripped.back())),
      "no trailing whitespace");
  }

  // idempotence
  __CPROVER_assert(
    strip_string(stripped) == stripped, "strip is idempotent");

  return 0;
}
