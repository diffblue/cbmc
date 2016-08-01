#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
    __CPROVER_string s;
    __CPROVER_char c1, c2;
    int i;
    int j;
    i = 2;
    s = __CPROVER_string_literal("pippo");
    c1 = __CPROVER_char_at(s, i);
    c2 = __CPROVER_char_literal("p");
    if (c1 == c2) {
        j = 1;
    }
    assert(j == 1);
    return 0;
}
