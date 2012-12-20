struct A{
	int i;
};

struct B: public A{
};

int main()
{
	B b;
	b.i=4;

	A(b).i++; // Not a lvalue?
	assert(b.i==4);
}
