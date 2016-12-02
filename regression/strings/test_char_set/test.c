#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s = __CPROVER_string_literal("abc");;
  char c = 'p';
  __CPROVER_string t = __CPROVER_char_set(s,1,c);;

  assert(__CPROVER_string_equal(t, __CPROVER_string_literal("apc")));
  assert(__CPROVER_string_equal(t, __CPROVER_string_literal("abc")));
  return 0;
}
