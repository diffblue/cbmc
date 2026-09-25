// Unit proof for trim_from_last_delimiter (src/util/string_utils.cpp).
//
// Verifies the function's contract over ALL strings up to a bounded
// length, built from nondeterministic printable characters:
//  * if the delimiter does not occur, the result is empty;
//  * otherwise the result is the prefix up to (excluding) the LAST
//    occurrence: it has that length, matches the input character-wise,
//    and the delimiter occurs nowhere after it in the input except at
//    the cut position... (the cut position holds the delimiter and no
//    later position does).
// Character scans in the SPEC are plain loops (std::string::find
// lowers to the memchr model, which loses pointer provenance).
// Single translation unit: include the implementation directly.
#include <util/string_utils.h>

#include "../../../src/util/string_utils.cpp"

extern "C" void __CPROVER_assert(bool, const char *);
extern "C" void __CPROVER_assume(bool);
int __VERIFIER_nondet_int();
char __VERIFIER_nondet_char();

#define MAX_LEN 4

static std::string nondet_string()
{
  int len = __VERIFIER_nondet_int();
  __CPROVER_assume(len >= 0 && len <= MAX_LEN);
  std::string s;
  for(int i = 0; i < len; ++i)
  {
    char c = __VERIFIER_nondet_char();
    __CPROVER_assume(c >= ' ' && c <= '~'); // printable
    s += c;
  }
  return s;
}

int main()
{
  std::string s = nondet_string();
  const char delim = '.';

  std::string trimmed = trim_from_last_delimiter(s, delim);

  // reference: position after which no delimiter occurs
  std::size_t last = s.size(); // npos-like sentinel
  for(std::size_t i = 0; i < s.size(); ++i)
    if(s[i] == delim)
      last = i;

  if(last == s.size())
  {
    __CPROVER_assert(trimmed.empty(), "no delimiter: empty result");
  }
  else
  {
    __CPROVER_assert(trimmed.size() == last, "cut at last delimiter");
    bool same = true;
    for(std::size_t i = 0; i < trimmed.size(); ++i)
      if(trimmed[i] != s[i])
        same = false;
    __CPROVER_assert(same, "result is a prefix of the input");
    bool none_after = true;
    for(std::size_t i = last + 1; i < s.size(); ++i)
      if(s[i] == delim)
        none_after = false;
    __CPROVER_assert(
      s[last] == delim && none_after, "cut position is the LAST delimiter");
  }

  return 0;
}
