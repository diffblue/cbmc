struct A
{
	int i;
	void func(){i  = 10;}
};

struct B: public A
{
	void (A::* pmeth)();
	B():
	  pmeth(&A::func)
	{
		(this->*pmeth)();
	}
};

int main()
{
	B b;
	assert(b.i == 10);
}
