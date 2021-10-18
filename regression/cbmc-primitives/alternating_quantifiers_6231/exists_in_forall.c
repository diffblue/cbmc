#include <stdlib.h>

// clang-format off
int main(int argc, char **argv)
{
    int *i = malloc(sizeof(int));
    *i = 1;

    __CPROVER_assert(
        __CPROVER_forall { int z; (0 < z && z < 10) ==>
            __CPROVER_exists { int y; ( 10 < y && y < 20) && y == z + 10 && y > *i } },
        "for all z, there exists a y so that y = z + 10 and y > 1");
}
// clang-format on
