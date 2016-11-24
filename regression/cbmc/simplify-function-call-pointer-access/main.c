#include <assert.h>

int f00 (int *pointer) {
        int i;
        for (i = 0; i < *pointer; ++i) {
                assert(i < 10);
        }
        return 0;
}

int main (void) {
        int limit = 0;
        f00(&limit);

        return 0;
}
