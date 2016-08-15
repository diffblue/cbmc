#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s,t,u;
  //s = __CPROVER_string_literal("pi");
  //t = __CPROVER_string_literal("ppo");
  unsigned i = __CPROVER_string_length(s);
  //t = __CPROVER_string_literal("ppo");
  __CPROVER_assume(i < 10);
  __CPROVER_assume(__CPROVER_string_equal(t, __CPROVER_string_literal("ppo")));
  u =  __CPROVER_string_concat(s, t);
  //assert(__CPROVER_char_at(u, 4) == __CPROVER_char_literal("o"));
  //assert(__CPROVER_string_equal(u, __CPROVER_string_literal("pippo")));
  
  __CPROVER_char c = __CPROVER_char_at(u,i);
 
  assert(c  == __CPROVER_char_literal("p"));
  return 0;
}
