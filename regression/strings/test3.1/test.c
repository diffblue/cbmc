#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
    __CPROVER_string s, s2, s3;
    int i;

    s = __CPROVER_string_concat(s2, s3);
    __CPROVER_assume(__CPROVER_string_length(s2) == i);
    __CPROVER_assume(__CPROVER_string_equal(s3, __CPROVER_string_literal("pippo")));

    // proving the assertions individually seems to be much faster
    assert(__CPROVER_string_length(s) == i + 5);
    //assert(__CPROVER_string_issuffix(__CPROVER_string_literal("po"), s));
    //assert(__CPROVER_char_at(s, i) == __CPROVER_char_literal("p"));

    return 0;
}
