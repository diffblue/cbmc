#include <assert.h>

int main(){

	int x[4];

	int y = x[3];
	
	x[0] = ++y;

	// assert c is tainted.
	assert(__CPROVER_is_taint("main::1::x[0]", "tainted"));

	return 0;
}
