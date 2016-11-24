struct A {
	int i;
	A(int i):i(i){}
};

class B: public A
{
	public:
	typedef A _A;
	B():_A(0){}
};

int main()
{
	B b;
	assert(b.i==0);
}
