#include <stdlib.h>

// clang-format off
int main(int argc, char **argv)
{
    int *i = malloc(sizeof(int));
    *i = 1;

    // The exists inside the assume will evaluate to true,
    // and as such, the assertion below will fail as expected.
    __CPROVER_assume(
        __CPROVER_exists{int z; (z > 1 && z < 10) && z > *i}
    );
    __CPROVER_assert(0, "this should come out as failure");
}
// clang-format on
