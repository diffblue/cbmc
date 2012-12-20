class A {
	int i;
	friend class B;
};

class B
{
	public:
	static int get(const A& a)
	{
		return a.i;
	}

	static void set(A& a, int i)
	{
		a.i = i;
	}
};

int main()
{

	A a;
	B::set(a,10);
	assert(B::get(a)==10);
}
