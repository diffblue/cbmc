struct A
{
	mutable int i;
	void set(int v) const
	{
		i = v;
	}
};

int main()
{
	const A a;
	a.set(99);
	assert(a.i==99);
}
