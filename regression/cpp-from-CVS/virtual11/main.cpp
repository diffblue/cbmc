struct A {
	int i;
	virtual operator int() const
	{
		return i;
	}
};

struct B : A
{
	operator int() const
	{
		return i+1;
	}
};

int get_i(const A& a)
{
	return a;
}

int main()
{
	B b;
	b.i = 10;
	assert(get_i(b)==11);
}
