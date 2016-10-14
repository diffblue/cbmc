#include <assert.h>
#include "../cprover-string-hack.h"

int main()
{
    __CPROVER_string s;
    int n;
    s = __CPROVER_string_literal("pippo");
    n = __CPROVER_string_length(s);
    assert(n == 5);
    assert(n != 5);
    return 0;
}
