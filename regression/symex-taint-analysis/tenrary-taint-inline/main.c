#include <assert.h>

struct name{
   int a;
   float b;
};
int main(){

	int x;

	__CPROVER_set_taint("main::1::x", "tainted");

	int y = 1;

	int z = 0;

	int c =  (z != y) ? x : y;

	assert(__CPROVER_is_taint("main::1::c", "tainted"));
	assert(__CPROVER_is_taint("main::1::x", "tainted"));
	assert(__CPROVER_is_taint("main::1::y", "untainted"));

    return 0;
}
