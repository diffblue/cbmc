// Note: systemc builtin extension
// require the cpp frontend to be compiled with the CPP_SYSTEMC_EXTENSION flag
int main()
{
	unsigned a = 6;
	unsigned b = 12;
	unsigned a21 =  a.range(2,1);
        unsigned b32	= b.range(3,2);
	assert( a21 == b32);

	a.range(4,3) = a.range(2,1);
	assert( a.range(4,3) == b.range(3,2));

	a[0] = b.range(3,3);
	bool a0 = a[0];
	assert(a0 == true);
}
