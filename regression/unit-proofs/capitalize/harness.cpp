// Unit proof for capitalize (src/util/string_utils.cpp).
//
// capitalize() upper-cases the first character and leaves everything
// else unchanged.  Proven over ALL strings up to MAX_LEN from the
// printable alphabet (nondeterministic inputs):
//  * size is preserved
//  * first character is the upper-cased original
//  * all other characters are unchanged
//  * idempotence: capitalize(capitalize(s)) == capitalize(s)
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
  for(int i = 0; i < MAX_LEN; ++i)
  {
    char c = __VERIFIER_nondet_char();
    __CPROVER_assume(c >= 0x20 && c <= 0x7e); // printable
    buf[i] = c;
  }
  buf[len] = '\0';
  const std::string input(buf, len);

  const std::string result = capitalize(input);

  __CPROVER_assert(result.size() == input.size(), "size preserved");

  if(!input.empty())
  {
    __CPROVER_assert(
      result.front() ==
        static_cast<char>(toupper(static_cast<unsigned char>(input.front()))),
      "first character upper-cased");
    for(std::size_t i = 1; i < input.size(); i++)
      __CPROVER_assert(result[i] == input[i], "tail unchanged");
  }

  const std::string twice = capitalize(result);
  __CPROVER_assert(twice == result, "idempotence");

  return 0;
}
