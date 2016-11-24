struct  A {
	int a;
};

struct B
{
	void f()
	{
		A::a = 1;    // ill-formed
		
	}
};
