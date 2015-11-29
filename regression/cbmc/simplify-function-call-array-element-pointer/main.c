#include <assert.h>

int array [4] = {0, 1, 2, 3};

int f00 (int *pointer) {
        int i;
        for (i = 0; i < *pointer; ++i) {
                assert(i < 10);
        }
        return 0;
}

int main (void) {
        f00(&(array[0]));

        return 0;
}
