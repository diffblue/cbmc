#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s;
  int i = 10;
  s = __CPROVER_string_of_int(123);
  assert(__CPROVER_char_at(s,0)  == '1');
  assert(__CPROVER_char_at(s,1)  == '2');

  int j = __CPROVER_parse_int(__CPROVER_string_literal("234"));

  assert(j == 234);
  assert(j < 233 || __CPROVER_char_at(s,2)  == '4');
  return 0;
}
