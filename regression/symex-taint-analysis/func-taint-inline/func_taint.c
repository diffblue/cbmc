#include <assert.h>
#include <stdlib.h>


int main(){

	int *x = malloc(sizeof(int));

	__CPROVER_set_taint("main::1::x", "tainted");

	*x = 9;

	int *y = x;

	assert(__CPROVER_is_taint("main::1::y", "tainted"));
	free(y);

    return 0;
}
