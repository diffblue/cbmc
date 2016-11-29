#include <assert.h>

struct name{
   int a;
   float b;
};
int main(){

	int x;

	__CPROVER_set_taint("main::1::x", "tainted");

	struct name my_name;
	my_name.a = x;

	assert(__CPROVER_is_taint("main::1::my_name.b", "untainted"));

    return 0;
}
