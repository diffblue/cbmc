int a[__CPROVER::constant_infinity_uint];

struct A {
	int i[__CPROVER::constant_infinity_uint];
};

A o;

int main()
{
	unsigned x;
	assert(o.i[x] == 0);
	assert(a[x] == 0);
}
