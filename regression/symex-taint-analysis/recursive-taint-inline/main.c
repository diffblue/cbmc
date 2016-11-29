#include <assert.h>

int factorial(unsigned int i) {

	if (i <= 1) {
		return 1;
	}
	return i * factorial(i - 1);
}

int main() {

	unsigned int x = 80;

	__CPROVER_set_taint("main::1::x", "tainted");

	unsigned int y = factorial(x);
	
	assert(__CPROVER_is_taint("main::1::y", "tainted"));

	return 0;
}
