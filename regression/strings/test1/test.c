#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
    __CPROVER_string s;
    char c1, c2;
    int i;
    int j;
    i = 2;
    s = __CPROVER_string_literal("pippo");
    c1 = __CPROVER_char_at(s, i);
    c2 = 'p';
    assert (c1 == c2);
    assert (c1 != c2);
    return 0;
}
