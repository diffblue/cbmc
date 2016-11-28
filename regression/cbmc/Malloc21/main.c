// Reported by Truc Nguyen Lam
// counter example looks supurious
// probably an error in bit-blasting somewhere
// show-vcc has reference to both dynamic_object and dynamic_object#1
// note that setting len to a constant breaks things
#include <assert.h>
#include <stdlib.h>

int v1;

int __VERIFIER_nondet_int();

int *data;
int len;

int main(void)
{
    v1 = __VERIFIER_nondet_int();
    __CPROVER_assume( (v1 > 0 ) & (v1 <= 2));

    if (!(v1 <= 0)) {
        len = __VERIFIER_nondet_int();
	__CPROVER_assume(len > 0);
	data = malloc(len * sizeof(int));
    }

    data[0] = 0;
    int tmp = data[0];
    assert(tmp == 0);

    return 0;
}
