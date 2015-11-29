#include <assert.h>

int main (void) {
        int i;
        int limit = 0;
        int *pointer = &limit;

        for (i = 0; i < *pointer; ++i) {
                assert(i < 10);
        }

        return 0;
}
