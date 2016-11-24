class A
{
	public:
	virtual int number(){return 0;}
};

class B: A
{
	public:
	int number(){return 1;}
	void test()
	{
		int n1 = number();
		assert(n1==1);
		int n2 = ::A::number();
		assert(n2 == 0);
	}
};

int main()
{
	B b;
	b.test();
}
