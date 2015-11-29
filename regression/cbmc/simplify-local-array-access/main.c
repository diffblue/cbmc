#include <assert.h>

int main (void) {
        int i;
        int array[4] = {0, 1, 2, 3};

        for (i = 0; i < array[0]; ++i) {
                assert(i < 10);
        }

        return 0;
}
