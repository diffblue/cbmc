struct A
{
	int i;
};

struct B: public A {
	int j;
};

int func(A a)
{
	return a.i;
}

int main()
{
	B b;
	b.i = 1;

	assert((* ((A*)&b)).i == 1); // This works fine.

	int  bi = func( * ((A*)&b)); // Satabs Ok.
	                             // cbmc error	
	assert(bi == 1);
}
