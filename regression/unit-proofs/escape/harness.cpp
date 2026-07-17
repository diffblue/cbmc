// Unit proof for escape (src/util/string_utils.cpp).
//
// escape() prefixes every backslash and double-quote with a backslash.
// The unit-test methodology spot-checks samples; this harness proves,
// over ALL strings up to MAX_LEN from the printable alphabet:
//  * length: |escape(s)| == |s| + #escapable(s)
//  * round-trip: dropping one backslash before each escaped character
//    (the inverse transformation, applied to the char data) yields the
//    original string
#include <util/string_utils.h>

// Single translation unit: the front end does not yet merge identical
// inline member definitions across translation units ([basic.def.odr]).
#include "../../../src/util/string_utils.cpp"

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
  std::size_t escapable = 0;
  for(int i = 0; i < MAX_LEN; ++i)
  {
    char c = __VERIFIER_nondet_char();
    __CPROVER_assume(c >= 0x20 && c <= 0x7e); // printable
    if(i < len && (c == '\\' || c == '"'))
      escapable++;
    buf[i] = c;
  }
  buf[len] = '\0';
  const std::string input(buf, len);

  const std::string escaped = escape(input);

  __CPROVER_assert(
    escaped.size() == input.size() + escapable, "escaped length");

  // inverse transformation over the char data, without further
  // std::string machinery: skip one backslash before each literal
  std::size_t j = 0;
  bool round_trip = true;
  for(std::size_t i = 0; i < escaped.size() && j <= input.size(); i++)
  {
    char c = escaped[i];
    if(c == '\\' && i + 1 < escaped.size())
      c = escaped[++i]; // escaped literal
    if(j >= input.size() || c != input[j])
    {
      round_trip = false;
      break;
    }
    j++;
  }
  __CPROVER_assert(
    round_trip && j == input.size(), "unescape round-trip");

  return 0;
}
