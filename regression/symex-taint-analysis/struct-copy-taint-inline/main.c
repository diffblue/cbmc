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
	my_name.b = -2.1459f;

	struct name my_name_copy;
	my_name_copy.a = my_name.a;
	my_name_copy.b = my_name.b;

	assert(__CPROVER_is_taint("main::1::my_name_copy.a", "tainted"));

    return 0;
}
