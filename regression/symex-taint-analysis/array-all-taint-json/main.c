#include <assert.h>

int main(){

	int x[4];

	int y = x[0];

	int c = ++y;

	// assert c is tainted.
	assert(__CPROVER_is_taint("main::1::c", "tainted"));

	return 0;
}
