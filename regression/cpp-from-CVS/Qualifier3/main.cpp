struct A
{
	int f();
};

struct B
{
	int g()
	{
		A::f(); // ill-formed
	}
};
