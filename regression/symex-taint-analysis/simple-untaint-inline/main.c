#include <assert.h>

int main(){

	int x;

	__CPROVER_set_taint("main::1::x", "tainted");

	int y = x;
	
	int c = y + 8;

	// c is set an immediate value.
	c = 0;

	// assert that c is not tainted.
	assert(!__CPROVER_is_taint("main::1::c", "tainted"));

	return 0;
}
