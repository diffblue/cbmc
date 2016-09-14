#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s;
  unsigned i = 10;
  s = __CPROVER_string_of_int(123);
  assert(__CPROVER_char_at(s,0)  == '1');
  assert(__CPROVER_char_at(s,1)  == '2');
  assert(__CPROVER_char_at(s,2)  == '4');
  return 0;
}
