struct A
{
	int i;
	A():i(0){}
	A(int i):i(i){}
};

struct B
{
	int j;
	B():j(0){}
	B(int j): j(j){}
	B(const A& a):j(a.i){}
};

B operator+(const B b1, B b2)
{
	return B( b1.j + b2.j );
}

int main()
{
	A a(10);
	B b = a + a;
	assert(b.j == 20);
}
