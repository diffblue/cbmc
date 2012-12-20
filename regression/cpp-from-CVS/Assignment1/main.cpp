struct A { int i;};

struct B
{
	int i;
	B& operator = (const B& b)
	{
		i = b.i;
		return *this;
	}
};

A funcA()
{
	A a;
	a.i = 10;
	return a;
}


B funcB()
{
	B b;
	b.i = 10;
	return b;
}

int main()
{
	A a;
	a.i = 20;
	assert((funcA() = a).i == 20); // legal

	B b;
	b.i = 20;
	assert((funcB() = b).i == 20);  // legal
}
