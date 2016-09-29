#include <assert.h>

int main(){

	int x;

	// taint propagation from x to y.
	int y = x;
	
	// taint propagation from y to c.
	int c = y + 7;

	// assert c is tainted.
	assert(__CPROVER_is_taint("main::1::c", "tainted"));

	return 0;
}
