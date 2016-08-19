#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s,t;
  int len_s, len_t;
  s = __CPROVER_string_literal("abc");
  t = __CPROVER_string_literal("xyz");
  len_s = __CPROVER_string_length(s);
  len_t = __CPROVER_string_length(t);
  assert(len_s == len_t);
  assert(len_s == 2);
  return 0;
}
