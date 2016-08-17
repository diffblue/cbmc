#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
  __CPROVER_string s1,s2,s3;
  __CPROVER_string t = __CPROVER_string_concat(s1,__CPROVER_string_concat(s2, s3));
  __CPROVER_assume(__CPROVER_string_equal(t, __CPROVER_string_literal("aaaa")));
  __CPROVER_assume(__CPROVER_string_length(s1) >= __CPROVER_string_length(s2));
  __CPROVER_assume(__CPROVER_string_length(s2) >= __CPROVER_string_length(s3));

  assert(__CPROVER_string_length(s3) == 0);
  assert(__CPROVER_string_length(s3) < 2);
  return 0;
}
