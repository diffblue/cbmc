#include <stdlib.h>

// clang-format off
int main(int argc, char **argv)
{
    int *i = malloc(sizeof(int));
    *i = 1;

    __CPROVER_assert(
        __CPROVER_exists { int z; (0 < z && z < 2) &&
            __CPROVER_forall { int o; (10 < o && o < 20) ==> o > z && z == * i }},
        "there exists a z between 0 and 2 so that for all o between 10 and 20, o > z and z = 1");
}
// clang-format on
