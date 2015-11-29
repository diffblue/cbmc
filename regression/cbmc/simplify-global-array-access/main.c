#include <assert.h>

int array[4] = {0, 1, 2, 3};

int main (void) {
        int i;

        for (i = 0; i < array[0]; ++i) {
                assert(i < 10);
        }

        return 0;
}
