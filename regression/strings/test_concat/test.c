#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s,t,u;
  unsigned i = __CPROVER_string_length(s);
  t = __CPROVER_string_literal("ppo");
  u =  __CPROVER_string_concat(s, t);
  __CPROVER_char c = __CPROVER_char_at(u,i);

  assert(c  == __CPROVER_char_literal("p"));
  assert(__CPROVER_char_at(u,2)  == __CPROVER_char_literal("p"));
  return 0;
}
