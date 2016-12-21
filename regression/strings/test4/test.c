#include <assert.h>
#include "../cprover-string-hack.h"


int main()
{
    __CPROVER_string s;
    int i;
    int j;
    i = 2;
    s = __CPROVER_string_literal("pippo");
    if (__CPROVER_char_at(s, i) == 'p') {
        j = 1;
    }
    assert(j == 1);
    return 0;
}
