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
	assert(func(b)==1);
}
