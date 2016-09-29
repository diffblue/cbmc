#include <assert.h>

struct name{
   int a;
   float b;
};
int main(){

	int x;

	__CPROVER_set_taint("main::1::x", "tainted");

	struct name nm;
	nm.a = x;

	assert(!__CPROVER_is_taint("main::1::nm.b", "tainted"));

    return 0;
}
