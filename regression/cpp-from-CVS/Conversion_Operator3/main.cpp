struct A {
	int i;
};

struct B {
	int i;
	operator A ()
	{
		A tmp;
		tmp.i = i++;
		return tmp;
	}
};

int main()
{
	B b;
	b.i = 1;
	A a = b;
	assert(a.i==1);
	assert(b.i==2);
}
