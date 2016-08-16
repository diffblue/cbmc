#include <assert.h>
#include "../cprover-string-hack.h"


void main()
{
    __CPROVER_string x, y, z, w;

    if (__CPROVER_string_equal(z, __CPROVER_string_concat(x, y)) &&
        __CPROVER_string_equal(z, __CPROVER_string_concat(w, __CPROVER_string_literal("c"))) &&
        __CPROVER_string_equal(__CPROVER_string_concat(__CPROVER_string_literal("c"), y), __CPROVER_string_concat(__CPROVER_string_literal("c"), __CPROVER_string_concat(__CPROVER_string_literal("b"), __CPROVER_string_literal("c"))))) {
        assert(0);
    }
}
