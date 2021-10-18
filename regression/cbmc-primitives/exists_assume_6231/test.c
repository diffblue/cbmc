#include <stdlib.h>

// clang-format off
int main(int argc, char **argv)
{
    int *i = malloc(sizeof(int));
    *i = 1;

    // The exists inside the assume will evaluate to true,
    // and be flipped by the negation in front of it, resulting
    // to assume(false), which will allow the assertion to evaluate
    // to true. 
    __CPROVER_assume(
        !__CPROVER_exists{int z; (z > 1 && z < 10) && z > *i}
    );
    __CPROVER_assert(0, "this assertion should be satified");
}
// clang-format on
