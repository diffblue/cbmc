#include <assert.h>

int array [4] = { 0, 1, 2, 3 };

int lookup (int *table) {
        int limit = table[0];
        int i;

        for (i = 0; i < limit; ++i) {
                assert(i < 10);
        }

        return 1;
}

int main (void) {
        lookup(array);

        return 0;
}
