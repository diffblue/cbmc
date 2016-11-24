#include <assert.h>

int main (void) {
	int x;

	while ((x + 1) -x != 1) {
		assert(0);
	}

	return 0;
}
