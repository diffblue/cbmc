#include <assert.h>
#include "../cprover-string-hack.h"
#define false 0
#define true 1

int main(){
  __CPROVER_string str;
  int firstSlash = __CPROVER_string_index_of(str,'/');
  //__CPROVER_char_literal("/"));
  int lastSlash = __CPROVER_string_last_index_of(str,'/');

  __CPROVER_assume(__CPROVER_string_equal(str, __CPROVER_string_literal("abc/abc/abc")));

  assert(firstSlash == 3);
  assert(lastSlash == 7);

  assert(firstSlash != 3 || lastSlash != 7);

  return 0;
}
