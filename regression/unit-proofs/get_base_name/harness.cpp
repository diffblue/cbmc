// Unit proof for get_base_name (src/util/get_base_name.cpp).
//
// Verifies the function's contract over ALL strings up to a bounded
// length, built from nondeterministic printable characters:
//  * the result never contains a path separator '/';
//  * without strip_suffix the result is exactly the substring after the
//    last '/' (in particular, a string without '/' is returned
//    unchanged);
//  * with strip_suffix the result is a prefix of the plain base name.
// Character scans in the SPEC are written as plain loops:
// std::string::find(char) lowers to char_traits/memchr, whose CBMC
// model loses pointer provenance (pointer-difference checks fire
// spuriously); the unit under proof only uses rfind/substr.
// Single translation unit: include the implementation directly.
#include <util/get_base_name.h>

#include "../../../src/util/get_base_name.cpp"

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

static bool contains(const std::string &s, char c)
{
  for(std::size_t i = 0; i < s.size(); ++i)
    if(s[i] == c)
      return true;
  return false;
}

int main()
{
  std::string s = nondet_string();

  std::string base = get_base_name(s, false);
  std::string stem = get_base_name(s, true);

  // no separator survives
  __CPROVER_assert(!contains(base, '/'), "base name has no separator");

  // exact tail: everything after the last '/'
  std::size_t start = s.size();
  while(start > 0 && s[start - 1] != '/')
    --start;
  __CPROVER_assert(base.size() == s.size() - start, "tail length");
  bool tail_equal = true;
  for(std::size_t i = 0; i < base.size(); ++i)
    if(base[i] != s[start + i])
      tail_equal = false;
  __CPROVER_assert(tail_equal, "base name is the tail");

  // the stem is a prefix of the base name
  bool prefix = stem.size() <= base.size();
  for(std::size_t i = 0; prefix && i < stem.size(); ++i)
    if(stem[i] != base[i])
      prefix = false;
  __CPROVER_assert(prefix, "stem is a prefix of the base name");

  return 0;
}
