#include <assert.h>

int main(){

	int x;

	__CPROVER_set_taint("main::1::x", "tainted");

	int y = 1;

	int z = 0;

	int c =  (z == y) ? x : y;

	assert(__CPROVER_is_taint("main::1::c", "untainted"));
	assert(__CPROVER_is_taint("main::1::z", "untainted"));
	assert(__CPROVER_is_taint("main::1::y", "untainted"));

    return 0;
}
