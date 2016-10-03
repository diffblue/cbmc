#include <assert.h>

int main(){

	int y;

	__CPROVER_set_taint("main::1::y", "tainted");

	int *x = &y;

	int *c = x;

	int z = *x;

	assert(__CPROVER_is_taint("main::1::y", "tainted"));
	assert(__CPROVER_is_taint("main::1::z", "tainted"));
	assert(__CPROVER_is_taint("main::1::x", "untainted"));
	assert(__CPROVER_is_taint("main::1::c", "untainted"));


	return 0;
}
