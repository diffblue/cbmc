struct A
{
	int i;
};

struct B: A
{
	typedef A _A;
	int i;
	void set(int i)
	{
		_A::i = i;
	}
	int get()
	{
		return _A::i;
	}
};

int main()
{
	B b;
	b.i = 0;
	b.set(3);
	assert(b.i==0);
	assert(b.get()== 3);
}
