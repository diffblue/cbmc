class A
{
	public:
	int a;
	int b;
	A(const A& r){b =~r.b;}
	A(){};
};

A a1;
A a2 = a1;
int main()
{
	assert(a1.a==0);
	assert(a2.a==0);
	assert(a1.b==0);
	assert(a2.b==~0);
};
