#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s,t;
  unsigned len_s, len_t;
  s = __CPROVER_string_literal("abc");
  t = __CPROVER_string_literal("xyz");
  len_s = __CPROVER_string_length(s);
  len_t = __CPROVER_string_length(t);
  unsigned b = ( len_s == len_t );
  assert(b);
  return 0;
}
