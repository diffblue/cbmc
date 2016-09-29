#include <assert.h>

int main(){

	int x[4];

	__CPROVER_set_taint("main::1::x[3]", "tainted");

	int y = x[3];
	
	x[0] = ++y;

	// assert c is tainted.
	assert(__CPROVER_is_taint("main::1::x[0]", "tainted"));

	return 0;
}
